# Retire the DIG deployment on Taco

The live DIG site now uses this architecture:

```text
https://dig.roars.dev
        -> Cloudflare Tunnel
        -> Prime 127.0.0.1:5001
        -> DIG frontend and API
```

Complete the checks below before deleting anything from Taco. Commands in the
Taco sections must be run on Taco, not Prime.

For the reversible Taco shutdown and key revocation described below, the
scripted path is:

```bash
sudo -u webapp git -C /home/webapp/dig pull --ff-only origin dev
sudo /home/webapp/dig/web/retire-taco.sh
```

After the rollback period, archive the obsolete service definitions and ngrok
configuration with:

```bash
sudo /home/webapp/dig/web/retire-taco.sh --finalize
```

If the script reports multiple forced deployment keys, inspect the redacted
entries it prints. If every match belongs to this retired DIG deployment, run:

```bash
sudo /home/webapp/dig/web/retire-taco.sh --finalize --all-deploy-keys
```

## 1. Verify Prime before retiring Taco

From any internet-connected machine:

```bash
curl --fail https://dig.roars.dev/api/health
```

Open <https://dig.roars.dev>, load an example, and confirm that **Run DIG**
finishes successfully.

On Prime:

```bash
sudo systemctl is-active dig-backend.service
sudo systemctl is-active cloudflared.service
curl --fail http://127.0.0.1:5001/api/health
```

All three checks should succeed before continuing.

## 2. Confirm that GitHub no longer deploys to Taco

The migration was pushed to `dev` in commit `f42271e`. In GitHub:

1. Open `dynaroars/dig`.
2. Select **Actions**.
3. Confirm that the workflow is named **Validate Prime deployment**.
4. Open its latest run and confirm that there is no `deploy-backend` job, SSH
   command, or reference to `taco.roars.dev`.

The current workflow validates deployment files only. It does not deploy to
Taco, GitHub Pages, or Prime.

## 3. Delete the Taco deployment secret from GitHub

Status: completed on 2026-09-09 for the repository-level
`TACO_DEPLOY_SSH_KEY`.

In `dynaroars/dig`:

1. Open **Settings**.
2. Select **Secrets and variables** -> **Actions**.
3. Under repository secrets, delete `TACO_DEPLOY_SSH_KEY`.
4. Check the **Environments** section for environment-level copies of the same
   secret and delete them if present.
5. If the repository inherited the secret from the `dynaroars` organization,
   check the organization's **Settings** -> **Secrets and variables** ->
   **Actions**. Remove this repository from that secret's access list, or delete
   the secret if no other repository uses it.

Do not delete unrelated GitHub Actions secrets.

## 4. Disable GitHub Pages

Status: completed on 2026-09-09. The GitHub Pages API now reports that no Pages
site is configured for `dynaroars/dig`.

The live frontend is now served by Prime, not GitHub Pages.

1. In `dynaroars/dig`, open **Settings** -> **Pages**.
2. Under the publishing source/build section, disable or unpublish the Pages
   site if GitHub offers that option.
3. Remove `dig.roars.dev` from the Pages **Custom domain** field if it is still
   configured there.
4. In Cloudflare DNS, confirm that `dig.roars.dev` points to the `dig-prime`
   tunnel and not to `dynaroars.github.io` or a GitHub Pages IP address.

Do not delete the GitHub repository. GitHub remains the source-code host.

## 5. Stop DIG on Taco

Connect to Taco using the administrative access that remains available:

```bash
ssh taco.roars.dev
```

Inspect the two DIG services before stopping them:

```bash
sudo systemctl status dig-backend.service --no-pager
sudo systemctl status dig-ngrok-tunnel.service --no-pager
```

Stop and disable only those services:

```bash
sudo systemctl disable --now dig-ngrok-tunnel.service
sudo systemctl disable --now dig-backend.service
```

Verify the result:

```bash
systemctl is-active dig-ngrok-tunnel.service
systemctl is-active dig-backend.service
systemctl is-enabled dig-ngrok-tunnel.service
systemctl is-enabled dig-backend.service
```

Expected state:

```text
inactive
inactive
disabled
disabled
```

The rollback is:

```bash
sudo systemctl enable --now dig-backend.service dig-ngrok-tunnel.service
```

## 6. Revoke GitHub's deployment key on Taco

The former workflow connected as `webapp`. Inspect its authorized keys:

```bash
sudo grep -nE 'deploy|DIG|github' /home/webapp/.ssh/authorized_keys
sudoedit /home/webapp/.ssh/authorized_keys
```

Remove only the line belonging to the DIG GitHub Actions deployment key. It may
contain a forced command such as `command="deploy"`. Do not remove keys used by
administrators or other applications.

After editing, preserve secure permissions:

```bash
sudo chown webapp:webapp /home/webapp/.ssh/authorized_keys
sudo chmod 600 /home/webapp/.ssh/authorized_keys
```

## 7. Retire the ngrok endpoint

In the ngrok dashboard:

1. Locate `density-capillary-thinning.ngrok-free.dev`.
2. Stop or delete its endpoint.
3. Release its reserved domain if it will not be reused.
4. Revoke the associated ngrok credential if it was dedicated to DIG.

Stopping `dig-ngrok-tunnel.service` should already make the endpoint offline,
but deleting the endpoint and credential prevents accidental reuse.

## 8. Observe before deleting Taco files

Keep the disabled Taco installation for a short rollback period, such as seven
days. During that period, verify Prime regularly:

```bash
curl --fail https://dig.roars.dev/api/health
```

Also confirm that the old ngrok endpoint no longer reaches DIG.

## 9. Optional permanent cleanup on Taco

Only perform this section after the rollback period and after confirming that
the paths belong exclusively to DIG.

First inspect the targets:

```bash
sudo systemctl cat dig-backend.service
sudo systemctl cat dig-ngrok-tunnel.service
sudo systemctl show -p FragmentPath dig-backend.service dig-ngrok-tunnel.service
sudo du -sh /home/webapp/dig
sudo ls -ld /home/webapp/dig /home/webapp/ngrok-dig.yml
```

Continue only if `FragmentPath` identifies the two expected files under
`/etc/systemd/system`. Remove those obsolete definitions and reload systemd:

```bash
sudo rm /etc/systemd/system/dig-backend.service
sudo rm /etc/systemd/system/dig-ngrok-tunnel.service
sudo systemctl daemon-reload
```

Instead of immediately deleting the old checkout and ngrok configuration, move
them into a dated archive directory:

```bash
sudo install -d -m 0700 /var/backups/dig-taco-retired
sudo mv /home/webapp/dig /var/backups/dig-taco-retired/
sudo mv /home/webapp/ngrok-dig.yml /var/backups/dig-taco-retired/
```

If either source path does not exist, skip that individual `mv` command. Delete
the archive only after it is no longer needed and according to the server's
backup-retention policy.

## 10. Final verification

On Taco, confirm that no DIG or ngrok process remains:

```bash
ps aux | grep -E '[g]unicorn.*DIG|[n]grok.*5001|[d]ig-backend'
sudo ss -ltnp | grep ':5001' || true
```

On Prime and externally:

```bash
sudo systemctl is-active dig-backend.service cloudflared.service
curl --fail http://127.0.0.1:5001/api/health
curl --fail https://dig.roars.dev/api/health
```

When Taco has no DIG processes, the old ngrok endpoint is retired, GitHub has no
Taco key or deployment job, and the public health check succeeds through Prime,
the Taco retirement is complete.
