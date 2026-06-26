def pytest_addoption(parser):
    parser.addoption(
        "--dig-timeout", type=int, default=180,
        help="per-program timeout (secs) for a DIG run",
    )
