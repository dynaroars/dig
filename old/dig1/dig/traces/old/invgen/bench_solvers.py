  


<!DOCTYPE html>
<html>
  <head prefix="og: http://ogp.me/ns# fb: http://ogp.me/ns/fb# githubog: http://ogp.me/ns/fb/githubog#">
    <meta charset='utf-8'>
    <meta http-equiv="X-UA-Compatible" content="IE=edge">
        <title>sympy/sympy/polys/benchmarks/bench_solvers.py at sparse-polys · mattpap/sympy · GitHub</title>
    <link rel="search" type="application/opensearchdescription+xml" href="/opensearch.xml" title="GitHub" />
    <link rel="fluid-icon" href="https://github.com/fluidicon.png" title="GitHub" />
    <link rel="apple-touch-icon" sizes="57x57" href="/apple-touch-icon-114.png" />
    <link rel="apple-touch-icon" sizes="114x114" href="/apple-touch-icon-114.png" />
    <link rel="apple-touch-icon" sizes="72x72" href="/apple-touch-icon-144.png" />
    <link rel="apple-touch-icon" sizes="144x144" href="/apple-touch-icon-144.png" />
    <link rel="logo" type="image/svg" href="http://github-media-downloads.s3.amazonaws.com/github-logo.svg" />
    <link rel="xhr-socket" href="/_sockets">
    <meta name="msapplication-TileImage" content="/windows-tile.png">
    <meta name="msapplication-TileColor" content="#ffffff">

    
    
    <link rel="icon" type="image/x-icon" href="/favicon.ico" />

    <meta content="authenticity_token" name="csrf-param" />
<meta content="reYp3W2MZ1LnKcaScu9LfzTNYzRUUlFmwZdfDoHgldI=" name="csrf-token" />

    <link href="https://a248.e.akamai.net/assets.github.com/assets/github-6fa026e7b63db8831643bd8cf0cf92483d7e827e.css" media="all" rel="stylesheet" type="text/css" />
    <link href="https://a248.e.akamai.net/assets.github.com/assets/github2-7a4dbbe68d3ae5fa8a5f35a6d6079c2295669ee7.css" media="all" rel="stylesheet" type="text/css" />
    


      <script src="https://a248.e.akamai.net/assets.github.com/assets/frameworks-b3959aea950ea4ce6b1c32c0ef079fc40bfb5f55.js" type="text/javascript"></script>
      <script src="https://a248.e.akamai.net/assets.github.com/assets/github-e9a5c794e3f48e4db032833f6bf5943e0896b96a.js" type="text/javascript"></script>
      
      <meta http-equiv="x-pjax-version" content="b9e1eb0da3fdcf3cf48f0f5c650c1458">

        <link data-pjax-transient rel='permalink' href='/mattpap/sympy/blob/aeb4c3684a22cb314b014fc92d9ea9b4b257ee2f/sympy/polys/benchmarks/bench_solvers.py'>
    <meta property="og:title" content="sympy"/>
    <meta property="og:type" content="githubog:gitrepository"/>
    <meta property="og:url" content="https://github.com/mattpap/sympy"/>
    <meta property="og:image" content="https://secure.gravatar.com/avatar/89164142ec718a76a7e04481062acaea?s=420&amp;d=https://a248.e.akamai.net/assets.github.com%2Fimages%2Fgravatars%2Fgravatar-user-420.png"/>
    <meta property="og:site_name" content="GitHub"/>
    <meta property="og:description" content="sympy - The main development repo for SymPy"/>
    <meta property="twitter:card" content="summary"/>
    <meta property="twitter:site" content="@GitHub">
    <meta property="twitter:title" content="mattpap/sympy"/>

    <meta name="description" content="sympy - The main development repo for SymPy" />

      <meta name="robots" content="noindex, nofollow">
  <link href="https://github.com/mattpap/sympy/commits/sparse-polys.atom" rel="alternate" title="Recent Commits to sympy:sparse-polys" type="application/atom+xml" />

  </head>


  <body class="logged_out page-blob  vis-public fork env-production  ">
    <div id="wrapper">

      

      
      
      

      
      <div class="header header-logged-out">
  <div class="container clearfix">

      <a class="header-logo-wordmark" href="https://github.com/">Github</a>

      <ul class="top-nav">
          <li class="explore"><a href="https://github.com/explore">Explore GitHub</a></li>
        <li class="search"><a href="https://github.com/search">Search</a></li>
        <li class="features"><a href="https://github.com/features">Features</a></li>
          <li class="blog"><a href="https://github.com/blog">Blog</a></li>
      </ul>

    <div class="header-actions">
        <a class="button primary" href="https://github.com/signup">Sign up for free</a>
      <a class="button" href="https://github.com/login?return_to=%2Fmattpap%2Fsympy%2Fblob%2Fsparse-polys%2Fsympy%2Fpolys%2Fbenchmarks%2Fbench_solvers.py">Sign in</a>
    </div>

  </div>
</div>


      

      


            <div class="site hfeed" itemscope itemtype="http://schema.org/WebPage">
      <div class="hentry">
        
        <div class="pagehead repohead instapaper_ignore readability-menu ">
          <div class="container">
            <div class="title-actions-bar">
              


<ul class="pagehead-actions">



    <li>
      <a href="/login?return_to=%2Fmattpap%2Fsympy"
        class="minibutton js-toggler-target star-button entice tooltipped upwards"
        title="You must be signed in to use this feature" rel="nofollow">
        <span class="mini-icon mini-icon-star"></span>Star
      </a>
      <a class="social-count js-social-count" href="/mattpap/sympy/stargazers">
        3
      </a>
    </li>
    <li>
      <a href="/login?return_to=%2Fmattpap%2Fsympy"
        class="minibutton js-toggler-target fork-button entice tooltipped upwards"
        title="You must be signed in to fork a repository" rel="nofollow">
        <span class="mini-icon mini-icon-fork"></span>Fork
      </a>
      <a href="/mattpap/sympy/network" class="social-count">
        384
      </a>
    </li>
</ul>

              <h1 itemscope itemtype="http://data-vocabulary.org/Breadcrumb" class="entry-title public">
                <span class="repo-label"><span>public</span></span>
                <span class="mega-icon mega-icon-public-repo"></span>
                <span class="author vcard">
                  <a href="/mattpap" class="url fn" itemprop="url" rel="author">
                  <span itemprop="title">mattpap</span>
                  </a></span> /
                <strong><a href="/mattpap/sympy" class="js-current-repository">sympy</a></strong>
                  <span class="fork-flag">
                    <span class="text">forked from <a href="/sympy/sympy">sympy/sympy</a></span>
                  </span>
              </h1>
            </div>

            
  <ul class="tabs">
    <li><a href="/mattpap/sympy/tree/sparse-polys" class="selected" highlight="repo_source repo_downloads repo_commits repo_tags repo_branches">Code</a></li>
    <li><a href="/mattpap/sympy/network" highlight="repo_network">Network</a></li>
    <li><a href="/mattpap/sympy/pulls" highlight="repo_pulls">Pull Requests <span class='counter'>0</span></a></li>


      <li><a href="/mattpap/sympy/wiki" highlight="repo_wiki">Wiki</a></li>


    <li><a href="/mattpap/sympy/graphs" highlight="repo_graphs repo_contributors">Graphs</a></li>


  </ul>
  
<div class="tabnav">

  <span class="tabnav-right">
    <ul class="tabnav-tabs">
          <li><a href="/mattpap/sympy/tags" class="tabnav-tab" highlight="repo_tags">Tags <span class="counter ">33</span></a></li>
    </ul>
    
  </span>

  <div class="tabnav-widget scope">


    <div class="select-menu js-menu-container js-select-menu js-branch-menu">
      <a class="minibutton select-menu-button js-menu-target" data-hotkey="w" data-ref="sparse-polys">
        <span class="mini-icon mini-icon-branch"></span>
        <i>branch:</i>
        <span class="js-select-button">sparse-polys</span>
      </a>

      <div class="select-menu-modal-holder js-menu-content js-navigation-container">

        <div class="select-menu-modal">
          <div class="select-menu-header">
            <span class="select-menu-title">Switch branches/tags</span>
            <span class="mini-icon mini-icon-remove-close js-menu-close"></span>
          </div> <!-- /.select-menu-header -->

          <div class="select-menu-filters">
            <div class="select-menu-text-filter">
              <input type="text" id="commitish-filter-field" class="js-filterable-field js-navigation-enable" placeholder="Filter branches/tags">
            </div>
            <div class="select-menu-tabs">
              <ul>
                <li class="select-menu-tab">
                  <a href="#" data-tab-filter="branches" class="js-select-menu-tab">Branches</a>
                </li>
                <li class="select-menu-tab">
                  <a href="#" data-tab-filter="tags" class="js-select-menu-tab">Tags</a>
                </li>
              </ul>
            </div><!-- /.select-menu-tabs -->
          </div><!-- /.select-menu-filters -->

          <div class="select-menu-list select-menu-tab-bucket js-select-menu-tab-bucket css-truncate" data-tab-filter="branches">

            <div data-filterable-for="commitish-filter-field" data-filterable-type="substring">

                <div class="select-menu-item js-navigation-item js-navigation-target ">
                  <span class="select-menu-item-icon mini-icon mini-icon-confirm"></span>
                  <a href="/mattpap/sympy/blob/apart-extension/sympy/polys/benchmarks/bench_solvers.py" class="js-navigation-open select-menu-item-text js-select-button-text css-truncate-target" data-name="apart-extension" rel="nofollow" title="apart-extension">apart-extension</a>
                </div> <!-- /.select-menu-item -->
                <div class="select-menu-item js-navigation-item js-navigation-target ">
                  <span class="select-menu-item-icon mini-icon mini-icon-confirm"></span>
                  <a href="/mattpap/sympy/blob/args_order/sympy/polys/benchmarks/bench_solvers.py" class="js-navigation-open select-menu-item-text js-select-button-text css-truncate-target" data-name="args_order" rel="nofollow" title="args_order">args_order</a>
                </div> <!-- /.select-menu-item -->
                <div class="select-menu-item js-navigation-item js-navigation-target ">
                  <span class="select-menu-item-icon mini-icon mini-icon-confirm"></span>
                  <a href="/mattpap/sympy/blob/arguments/sympy/polys/benchmarks/bench_solvers.py" class="js-navigation-open select-menu-item-text js-select-button-text css-truncate-target" data-name="arguments" rel="nofollow" title="arguments">arguments</a>
                </div> <!-- /.select-menu-item -->
                <div class="select-menu-item js-navigation-item js-navigation-target ">
                  <span class="select-menu-item-icon mini-icon mini-icon-confirm"></span>
                  <a href="/mattpap/sympy/blob/assert/sympy/polys/benchmarks/bench_solvers.py" class="js-navigation-open select-menu-item-text js-select-button-text css-truncate-target" data-name="assert" rel="nofollow" title="assert">assert</a>
                </div> <!-- /.select-menu-item -->
                <div class="select-menu-item js-navigation-item js-navigation-target ">
                  <span class="select-menu-item-icon mini-icon mini-icon-confirm"></span>
                  <a href="/mattpap/sympy/blob/auto_symbols/sympy/polys/benchmarks/bench_solvers.py" class="js-navigation-open select-menu-item-text js-select-button-text css-truncate-target" data-name="auto_symbols" rel="nofollow" title="auto_symbols">auto_symbols</a>
                </div> <!-- /.select-menu-item -->
                <div class="select-menu-item js-navigation-item js-navigation-target ">
                  <span class="select-menu-item-icon mini-icon mini-icon-confirm"></span>
                  <a href="/mattpap/sympy/blob/backport/sympy/polys/benchmarks/bench_solvers.py" class="js-navigation-open select-menu-item-text js-select-button-text css-truncate-target" data-name="backport" rel="nofollow" title="backport">backport</a>
                </div> <!-- /.select-menu-item -->
                <div class="select-menu-item js-navigation-item js-navigation-target ">
                  <span class="select-menu-item-icon mini-icon mini-icon-confirm"></span>
                  <a href="/mattpap/sympy/blob/basic_args/sympy/polys/benchmarks/bench_solvers.py" class="js-navigation-open select-menu-item-text js-select-button-text css-truncate-target" data-name="basic_args" rel="nofollow" title="basic_args">basic_args</a>
                </div> <!-- /.select-menu-item -->
                <div class="select-menu-item js-navigation-item js-navigation-target ">
                  <span class="select-menu-item-icon mini-icon mini-icon-confirm"></span>
                  <a href="/mattpap/sympy/blob/cancel/sympy/polys/benchmarks/bench_solvers.py" class="js-navigation-open select-menu-item-text js-select-button-text css-truncate-target" data-name="cancel" rel="nofollow" title="cancel">cancel</a>
                </div> <!-- /.select-menu-item -->
                <div class="select-menu-item js-navigation-item js-navigation-target ">
                  <span class="select-menu-item-icon mini-icon mini-icon-confirm"></span>
                  <a href="/mattpap/sympy/blob/compare_pretty/sympy/polys/benchmarks/bench_solvers.py" class="js-navigation-open select-menu-item-text js-select-button-text css-truncate-target" data-name="compare_pretty" rel="nofollow" title="compare_pretty">compare_pretty</a>
                </div> <!-- /.select-menu-item -->
                <div class="select-menu-item js-navigation-item js-navigation-target ">
                  <span class="select-menu-item-icon mini-icon mini-icon-confirm"></span>
                  <a href="/mattpap/sympy/blob/complex-order/sympy/polys/benchmarks/bench_solvers.py" class="js-navigation-open select-menu-item-text js-select-button-text css-truncate-target" data-name="complex-order" rel="nofollow" title="complex-order">complex-order</a>
                </div> <!-- /.select-menu-item -->
                <div class="select-menu-item js-navigation-item js-navigation-target ">
                  <span class="select-menu-item-icon mini-icon mini-icon-confirm"></span>
                  <a href="/mattpap/sympy/blob/contains/sympy/polys/benchmarks/bench_solvers.py" class="js-navigation-open select-menu-item-text js-select-button-text css-truncate-target" data-name="contains" rel="nofollow" title="contains">contains</a>
                </div> <!-- /.select-menu-item -->
                <div class="select-menu-item js-navigation-item js-navigation-target ">
                  <span class="select-menu-item-icon mini-icon mini-icon-confirm"></span>
                  <a href="/mattpap/sympy/blob/converter/sympy/polys/benchmarks/bench_solvers.py" class="js-navigation-open select-menu-item-text js-select-button-text css-truncate-target" data-name="converter" rel="nofollow" title="converter">converter</a>
                </div> <!-- /.select-menu-item -->
                <div class="select-menu-item js-navigation-item js-navigation-target ">
                  <span class="select-menu-item-icon mini-icon mini-icon-confirm"></span>
                  <a href="/mattpap/sympy/blob/cse_test/sympy/polys/benchmarks/bench_solvers.py" class="js-navigation-open select-menu-item-text js-select-button-text css-truncate-target" data-name="cse_test" rel="nofollow" title="cse_test">cse_test</a>
                </div> <!-- /.select-menu-item -->
                <div class="select-menu-item js-navigation-item js-navigation-target ">
                  <span class="select-menu-item-icon mini-icon mini-icon-confirm"></span>
                  <a href="/mattpap/sympy/blob/cyclotomic/sympy/polys/benchmarks/bench_solvers.py" class="js-navigation-open select-menu-item-text js-select-button-text css-truncate-target" data-name="cyclotomic" rel="nofollow" title="cyclotomic">cyclotomic</a>
                </div> <!-- /.select-menu-item -->
                <div class="select-menu-item js-navigation-item js-navigation-target ">
                  <span class="select-menu-item-icon mini-icon mini-icon-confirm"></span>
                  <a href="/mattpap/sympy/blob/div/sympy/polys/benchmarks/bench_solvers.py" class="js-navigation-open select-menu-item-text js-select-button-text css-truncate-target" data-name="div" rel="nofollow" title="div">div</a>
                </div> <!-- /.select-menu-item -->
                <div class="select-menu-item js-navigation-item js-navigation-target ">
                  <span class="select-menu-item-icon mini-icon mini-icon-confirm"></span>
                  <a href="/mattpap/sympy/blob/enhanced-asserts/sympy/polys/benchmarks/bench_solvers.py" class="js-navigation-open select-menu-item-text js-select-button-text css-truncate-target" data-name="enhanced-asserts" rel="nofollow" title="enhanced-asserts">enhanced-asserts</a>
                </div> <!-- /.select-menu-item -->
                <div class="select-menu-item js-navigation-item js-navigation-target ">
                  <span class="select-menu-item-icon mini-icon mini-icon-confirm"></span>
                  <a href="/mattpap/sympy/blob/epath/sympy/polys/benchmarks/bench_solvers.py" class="js-navigation-open select-menu-item-text js-select-button-text css-truncate-target" data-name="epath" rel="nofollow" title="epath">epath</a>
                </div> <!-- /.select-menu-item -->
                <div class="select-menu-item js-navigation-item js-navigation-target ">
                  <span class="select-menu-item-icon mini-icon mini-icon-confirm"></span>
                  <a href="/mattpap/sympy/blob/exceptions/sympy/polys/benchmarks/bench_solvers.py" class="js-navigation-open select-menu-item-text js-select-button-text css-truncate-target" data-name="exceptions" rel="nofollow" title="exceptions">exceptions</a>
                </div> <!-- /.select-menu-item -->
                <div class="select-menu-item js-navigation-item js-navigation-target ">
                  <span class="select-menu-item-icon mini-icon mini-icon-confirm"></span>
                  <a href="/mattpap/sympy/blob/exceptions2/sympy/polys/benchmarks/bench_solvers.py" class="js-navigation-open select-menu-item-text js-select-button-text css-truncate-target" data-name="exceptions2" rel="nofollow" title="exceptions2">exceptions2</a>
                </div> <!-- /.select-menu-item -->
                <div class="select-menu-item js-navigation-item js-navigation-target ">
                  <span class="select-menu-item-icon mini-icon mini-icon-confirm"></span>
                  <a href="/mattpap/sympy/blob/exquo/sympy/polys/benchmarks/bench_solvers.py" class="js-navigation-open select-menu-item-text js-select-button-text css-truncate-target" data-name="exquo" rel="nofollow" title="exquo">exquo</a>
                </div> <!-- /.select-menu-item -->
                <div class="select-menu-item js-navigation-item js-navigation-target ">
                  <span class="select-menu-item-icon mini-icon mini-icon-confirm"></span>
                  <a href="/mattpap/sympy/blob/factor_power/sympy/polys/benchmarks/bench_solvers.py" class="js-navigation-open select-menu-item-text js-select-button-text css-truncate-target" data-name="factor_power" rel="nofollow" title="factor_power">factor_power</a>
                </div> <!-- /.select-menu-item -->
                <div class="select-menu-item js-navigation-item js-navigation-target ">
                  <span class="select-menu-item-icon mini-icon mini-icon-confirm"></span>
                  <a href="/mattpap/sympy/blob/factorials/sympy/polys/benchmarks/bench_solvers.py" class="js-navigation-open select-menu-item-text js-select-button-text css-truncate-target" data-name="factorials" rel="nofollow" title="factorials">factorials</a>
                </div> <!-- /.select-menu-item -->
                <div class="select-menu-item js-navigation-item js-navigation-target ">
                  <span class="select-menu-item-icon mini-icon mini-icon-confirm"></span>
                  <a href="/mattpap/sympy/blob/fix_log_to_real/sympy/polys/benchmarks/bench_solvers.py" class="js-navigation-open select-menu-item-text js-select-button-text css-truncate-target" data-name="fix_log_to_real" rel="nofollow" title="fix_log_to_real">fix_log_to_real</a>
                </div> <!-- /.select-menu-item -->
                <div class="select-menu-item js-navigation-item js-navigation-target ">
                  <span class="select-menu-item-icon mini-icon mini-icon-confirm"></span>
                  <a href="/mattpap/sympy/blob/fixes/sympy/polys/benchmarks/bench_solvers.py" class="js-navigation-open select-menu-item-text js-select-button-text css-truncate-target" data-name="fixes" rel="nofollow" title="fixes">fixes</a>
                </div> <!-- /.select-menu-item -->
                <div class="select-menu-item js-navigation-item js-navigation-target ">
                  <span class="select-menu-item-icon mini-icon mini-icon-confirm"></span>
                  <a href="/mattpap/sympy/blob/float_new/sympy/polys/benchmarks/bench_solvers.py" class="js-navigation-open select-menu-item-text js-select-button-text css-truncate-target" data-name="float_new" rel="nofollow" title="float_new">float_new</a>
                </div> <!-- /.select-menu-item -->
                <div class="select-menu-item js-navigation-item js-navigation-target ">
                  <span class="select-menu-item-icon mini-icon mini-icon-confirm"></span>
                  <a href="/mattpap/sympy/blob/full-apart/sympy/polys/benchmarks/bench_solvers.py" class="js-navigation-open select-menu-item-text js-select-button-text css-truncate-target" data-name="full-apart" rel="nofollow" title="full-apart">full-apart</a>
                </div> <!-- /.select-menu-item -->
                <div class="select-menu-item js-navigation-item js-navigation-target ">
                  <span class="select-menu-item-icon mini-icon mini-icon-confirm"></span>
                  <a href="/mattpap/sympy/blob/gcd_terms/sympy/polys/benchmarks/bench_solvers.py" class="js-navigation-open select-menu-item-text js-select-button-text css-truncate-target" data-name="gcd_terms" rel="nofollow" title="gcd_terms">gcd_terms</a>
                </div> <!-- /.select-menu-item -->
                <div class="select-menu-item js-navigation-item js-navigation-target ">
                  <span class="select-menu-item-icon mini-icon mini-icon-confirm"></span>
                  <a href="/mattpap/sympy/blob/gh-pages/sympy/polys/benchmarks/bench_solvers.py" class="js-navigation-open select-menu-item-text js-select-button-text css-truncate-target" data-name="gh-pages" rel="nofollow" title="gh-pages">gh-pages</a>
                </div> <!-- /.select-menu-item -->
                <div class="select-menu-item js-navigation-item js-navigation-target ">
                  <span class="select-menu-item-icon mini-icon mini-icon-confirm"></span>
                  <a href="/mattpap/sympy/blob/gosper/sympy/polys/benchmarks/bench_solvers.py" class="js-navigation-open select-menu-item-text js-select-button-text css-truncate-target" data-name="gosper" rel="nofollow" title="gosper">gosper</a>
                </div> <!-- /.select-menu-item -->
                <div class="select-menu-item js-navigation-item js-navigation-target ">
                  <span class="select-menu-item-icon mini-icon mini-icon-confirm"></span>
                  <a href="/mattpap/sympy/blob/groebner/sympy/polys/benchmarks/bench_solvers.py" class="js-navigation-open select-menu-item-text js-select-button-text css-truncate-target" data-name="groebner" rel="nofollow" title="groebner">groebner</a>
                </div> <!-- /.select-menu-item -->
                <div class="select-menu-item js-navigation-item js-navigation-target ">
                  <span class="select-menu-item-icon mini-icon mini-icon-confirm"></span>
                  <a href="/mattpap/sympy/blob/guessing/sympy/polys/benchmarks/bench_solvers.py" class="js-navigation-open select-menu-item-text js-select-button-text css-truncate-target" data-name="guessing" rel="nofollow" title="guessing">guessing</a>
                </div> <!-- /.select-menu-item -->
                <div class="select-menu-item js-navigation-item js-navigation-target ">
                  <span class="select-menu-item-icon mini-icon mini-icon-confirm"></span>
                  <a href="/mattpap/sympy/blob/has/sympy/polys/benchmarks/bench_solvers.py" class="js-navigation-open select-menu-item-text js-select-button-text css-truncate-target" data-name="has" rel="nofollow" title="has">has</a>
                </div> <!-- /.select-menu-item -->
                <div class="select-menu-item js-navigation-item js-navigation-target ">
                  <span class="select-menu-item-icon mini-icon mini-icon-confirm"></span>
                  <a href="/mattpap/sympy/blob/infinities/sympy/polys/benchmarks/bench_solvers.py" class="js-navigation-open select-menu-item-text js-select-button-text css-truncate-target" data-name="infinities" rel="nofollow" title="infinities">infinities</a>
                </div> <!-- /.select-menu-item -->
                <div class="select-menu-item js-navigation-item js-navigation-target ">
                  <span class="select-menu-item-icon mini-icon mini-icon-confirm"></span>
                  <a href="/mattpap/sympy/blob/integrate_series/sympy/polys/benchmarks/bench_solvers.py" class="js-navigation-open select-menu-item-text js-select-button-text css-truncate-target" data-name="integrate_series" rel="nofollow" title="integrate_series">integrate_series</a>
                </div> <!-- /.select-menu-item -->
                <div class="select-menu-item js-navigation-item js-navigation-target ">
                  <span class="select-menu-item-icon mini-icon mini-icon-confirm"></span>
                  <a href="/mattpap/sympy/blob/issue_2754-str-poly/sympy/polys/benchmarks/bench_solvers.py" class="js-navigation-open select-menu-item-text js-select-button-text css-truncate-target" data-name="issue_2754-str-poly" rel="nofollow" title="issue_2754-str-poly">issue_2754-str-poly</a>
                </div> <!-- /.select-menu-item -->
                <div class="select-menu-item js-navigation-item js-navigation-target ">
                  <span class="select-menu-item-icon mini-icon mini-icon-confirm"></span>
                  <a href="/mattpap/sympy/blob/issue3048/sympy/polys/benchmarks/bench_solvers.py" class="js-navigation-open select-menu-item-text js-select-button-text css-truncate-target" data-name="issue3048" rel="nofollow" title="issue3048">issue3048</a>
                </div> <!-- /.select-menu-item -->
                <div class="select-menu-item js-navigation-item js-navigation-target ">
                  <span class="select-menu-item-icon mini-icon mini-icon-confirm"></span>
                  <a href="/mattpap/sympy/blob/issue_3245-poly-eval/sympy/polys/benchmarks/bench_solvers.py" class="js-navigation-open select-menu-item-text js-select-button-text css-truncate-target" data-name="issue_3245-poly-eval" rel="nofollow" title="issue_3245-poly-eval">issue_3245-poly-eval</a>
                </div> <!-- /.select-menu-item -->
                <div class="select-menu-item js-navigation-item js-navigation-target ">
                  <span class="select-menu-item-icon mini-icon mini-icon-confirm"></span>
                  <a href="/mattpap/sympy/blob/issue_3256/sympy/polys/benchmarks/bench_solvers.py" class="js-navigation-open select-menu-item-text js-select-button-text css-truncate-target" data-name="issue_3256" rel="nofollow" title="issue_3256">issue_3256</a>
                </div> <!-- /.select-menu-item -->
                <div class="select-menu-item js-navigation-item js-navigation-target ">
                  <span class="select-menu-item-icon mini-icon mini-icon-confirm"></span>
                  <a href="/mattpap/sympy/blob/isympy-config/sympy/polys/benchmarks/bench_solvers.py" class="js-navigation-open select-menu-item-text js-select-button-text css-truncate-target" data-name="isympy-config" rel="nofollow" title="isympy-config">isympy-config</a>
                </div> <!-- /.select-menu-item -->
                <div class="select-menu-item js-navigation-item js-navigation-target ">
                  <span class="select-menu-item-icon mini-icon mini-icon-confirm"></span>
                  <a href="/mattpap/sympy/blob/linux3/sympy/polys/benchmarks/bench_solvers.py" class="js-navigation-open select-menu-item-text js-select-button-text css-truncate-target" data-name="linux3" rel="nofollow" title="linux3">linux3</a>
                </div> <!-- /.select-menu-item -->
                <div class="select-menu-item js-navigation-item js-navigation-target ">
                  <span class="select-menu-item-icon mini-icon mini-icon-confirm"></span>
                  <a href="/mattpap/sympy/blob/lpoly2-improved/sympy/polys/benchmarks/bench_solvers.py" class="js-navigation-open select-menu-item-text js-select-button-text css-truncate-target" data-name="lpoly2-improved" rel="nofollow" title="lpoly2-improved">lpoly2-improved</a>
                </div> <!-- /.select-menu-item -->
                <div class="select-menu-item js-navigation-item js-navigation-target ">
                  <span class="select-menu-item-icon mini-icon mini-icon-confirm"></span>
                  <a href="/mattpap/sympy/blob/master/sympy/polys/benchmarks/bench_solvers.py" class="js-navigation-open select-menu-item-text js-select-button-text css-truncate-target" data-name="master" rel="nofollow" title="master">master</a>
                </div> <!-- /.select-menu-item -->
                <div class="select-menu-item js-navigation-item js-navigation-target ">
                  <span class="select-menu-item-icon mini-icon mini-icon-confirm"></span>
                  <a href="/mattpap/sympy/blob/matrix_expr/sympy/polys/benchmarks/bench_solvers.py" class="js-navigation-open select-menu-item-text js-select-button-text css-truncate-target" data-name="matrix_expr" rel="nofollow" title="matrix_expr">matrix_expr</a>
                </div> <!-- /.select-menu-item -->
                <div class="select-menu-item js-navigation-item js-navigation-target ">
                  <span class="select-menu-item-icon mini-icon mini-icon-confirm"></span>
                  <a href="/mattpap/sympy/blob/message/sympy/polys/benchmarks/bench_solvers.py" class="js-navigation-open select-menu-item-text js-select-button-text css-truncate-target" data-name="message" rel="nofollow" title="message">message</a>
                </div> <!-- /.select-menu-item -->
                <div class="select-menu-item js-navigation-item js-navigation-target ">
                  <span class="select-menu-item-icon mini-icon mini-icon-confirm"></span>
                  <a href="/mattpap/sympy/blob/minus_sign/sympy/polys/benchmarks/bench_solvers.py" class="js-navigation-open select-menu-item-text js-select-button-text css-truncate-target" data-name="minus_sign" rel="nofollow" title="minus_sign">minus_sign</a>
                </div> <!-- /.select-menu-item -->
                <div class="select-menu-item js-navigation-item js-navigation-target ">
                  <span class="select-menu-item-icon mini-icon mini-icon-confirm"></span>
                  <a href="/mattpap/sympy/blob/modular_integer/sympy/polys/benchmarks/bench_solvers.py" class="js-navigation-open select-menu-item-text js-select-button-text css-truncate-target" data-name="modular_integer" rel="nofollow" title="modular_integer">modular_integer</a>
                </div> <!-- /.select-menu-item -->
                <div class="select-menu-item js-navigation-item js-navigation-target ">
                  <span class="select-menu-item-icon mini-icon mini-icon-confirm"></span>
                  <a href="/mattpap/sympy/blob/nargs_error/sympy/polys/benchmarks/bench_solvers.py" class="js-navigation-open select-menu-item-text js-select-button-text css-truncate-target" data-name="nargs_error" rel="nofollow" title="nargs_error">nargs_error</a>
                </div> <!-- /.select-menu-item -->
                <div class="select-menu-item js-navigation-item js-navigation-target ">
                  <span class="select-menu-item-icon mini-icon mini-icon-confirm"></span>
                  <a href="/mattpap/sympy/blob/new-polys/sympy/polys/benchmarks/bench_solvers.py" class="js-navigation-open select-menu-item-text js-select-button-text css-truncate-target" data-name="new-polys" rel="nofollow" title="new-polys">new-polys</a>
                </div> <!-- /.select-menu-item -->
                <div class="select-menu-item js-navigation-item js-navigation-target ">
                  <span class="select-menu-item-icon mini-icon mini-icon-confirm"></span>
                  <a href="/mattpap/sympy/blob/numbers_test_test/sympy/polys/benchmarks/bench_solvers.py" class="js-navigation-open select-menu-item-text js-select-button-text css-truncate-target" data-name="numbers_test_test" rel="nofollow" title="numbers_test_test">numbers_test_test</a>
                </div> <!-- /.select-menu-item -->
                <div class="select-menu-item js-navigation-item js-navigation-target ">
                  <span class="select-menu-item-icon mini-icon mini-icon-confirm"></span>
                  <a href="/mattpap/sympy/blob/order/sympy/polys/benchmarks/bench_solvers.py" class="js-navigation-open select-menu-item-text js-select-button-text css-truncate-target" data-name="order" rel="nofollow" title="order">order</a>
                </div> <!-- /.select-menu-item -->
                <div class="select-menu-item js-navigation-item js-navigation-target ">
                  <span class="select-menu-item-icon mini-icon mini-icon-confirm"></span>
                  <a href="/mattpap/sympy/blob/other_order/sympy/polys/benchmarks/bench_solvers.py" class="js-navigation-open select-menu-item-text js-select-button-text css-truncate-target" data-name="other_order" rel="nofollow" title="other_order">other_order</a>
                </div> <!-- /.select-menu-item -->
                <div class="select-menu-item js-navigation-item js-navigation-target ">
                  <span class="select-menu-item-icon mini-icon mini-icon-confirm"></span>
                  <a href="/mattpap/sympy/blob/p12-final/sympy/polys/benchmarks/bench_solvers.py" class="js-navigation-open select-menu-item-text js-select-button-text css-truncate-target" data-name="p12-final" rel="nofollow" title="p12-final">p12-final</a>
                </div> <!-- /.select-menu-item -->
                <div class="select-menu-item js-navigation-item js-navigation-target ">
                  <span class="select-menu-item-icon mini-icon mini-icon-confirm"></span>
                  <a href="/mattpap/sympy/blob/parser/sympy/polys/benchmarks/bench_solvers.py" class="js-navigation-open select-menu-item-text js-select-button-text css-truncate-target" data-name="parser" rel="nofollow" title="parser">parser</a>
                </div> <!-- /.select-menu-item -->
                <div class="select-menu-item js-navigation-item js-navigation-target ">
                  <span class="select-menu-item-icon mini-icon mini-icon-confirm"></span>
                  <a href="/mattpap/sympy/blob/pickling/sympy/polys/benchmarks/bench_solvers.py" class="js-navigation-open select-menu-item-text js-select-button-text css-truncate-target" data-name="pickling" rel="nofollow" title="pickling">pickling</a>
                </div> <!-- /.select-menu-item -->
                <div class="select-menu-item js-navigation-item js-navigation-target ">
                  <span class="select-menu-item-icon mini-icon mini-icon-confirm"></span>
                  <a href="/mattpap/sympy/blob/poly/sympy/polys/benchmarks/bench_solvers.py" class="js-navigation-open select-menu-item-text js-select-button-text css-truncate-target" data-name="poly" rel="nofollow" title="poly">poly</a>
                </div> <!-- /.select-menu-item -->
                <div class="select-menu-item js-navigation-item js-navigation-target ">
                  <span class="select-menu-item-icon mini-icon mini-icon-confirm"></span>
                  <a href="/mattpap/sympy/blob/poly-coeff/sympy/polys/benchmarks/bench_solvers.py" class="js-navigation-open select-menu-item-text js-select-button-text css-truncate-target" data-name="poly-coeff" rel="nofollow" title="poly-coeff">poly-coeff</a>
                </div> <!-- /.select-menu-item -->
                <div class="select-menu-item js-navigation-item js-navigation-target ">
                  <span class="select-menu-item-icon mini-icon mini-icon-confirm"></span>
                  <a href="/mattpap/sympy/blob/porting/sympy/polys/benchmarks/bench_solvers.py" class="js-navigation-open select-menu-item-text js-select-button-text css-truncate-target" data-name="porting" rel="nofollow" title="porting">porting</a>
                </div> <!-- /.select-menu-item -->
                <div class="select-menu-item js-navigation-item js-navigation-target ">
                  <span class="select-menu-item-icon mini-icon mini-icon-confirm"></span>
                  <a href="/mattpap/sympy/blob/pprint-sum/sympy/polys/benchmarks/bench_solvers.py" class="js-navigation-open select-menu-item-text js-select-button-text css-truncate-target" data-name="pprint-sum" rel="nofollow" title="pprint-sum">pprint-sum</a>
                </div> <!-- /.select-menu-item -->
                <div class="select-menu-item js-navigation-item js-navigation-target ">
                  <span class="select-menu-item-icon mini-icon mini-icon-confirm"></span>
                  <a href="/mattpap/sympy/blob/preprocessing/sympy/polys/benchmarks/bench_solvers.py" class="js-navigation-open select-menu-item-text js-select-button-text css-truncate-target" data-name="preprocessing" rel="nofollow" title="preprocessing">preprocessing</a>
                </div> <!-- /.select-menu-item -->
                <div class="select-menu-item js-navigation-item js-navigation-target ">
                  <span class="select-menu-item-icon mini-icon mini-icon-confirm"></span>
                  <a href="/mattpap/sympy/blob/pretty_derivative/sympy/polys/benchmarks/bench_solvers.py" class="js-navigation-open select-menu-item-text js-select-button-text css-truncate-target" data-name="pretty_derivative" rel="nofollow" title="pretty_derivative">pretty_derivative</a>
                </div> <!-- /.select-menu-item -->
                <div class="select-menu-item js-navigation-item js-navigation-target ">
                  <span class="select-menu-item-icon mini-icon mini-icon-confirm"></span>
                  <a href="/mattpap/sympy/blob/pretty_lambda/sympy/polys/benchmarks/bench_solvers.py" class="js-navigation-open select-menu-item-text js-select-button-text css-truncate-target" data-name="pretty_lambda" rel="nofollow" title="pretty_lambda">pretty_lambda</a>
                </div> <!-- /.select-menu-item -->
                <div class="select-menu-item js-navigation-item js-navigation-target ">
                  <span class="select-menu-item-icon mini-icon mini-icon-confirm"></span>
                  <a href="/mattpap/sympy/blob/pretty_noncommutative/sympy/polys/benchmarks/bench_solvers.py" class="js-navigation-open select-menu-item-text js-select-button-text css-truncate-target" data-name="pretty_noncommutative" rel="nofollow" title="pretty_noncommutative">pretty_noncommutative</a>
                </div> <!-- /.select-menu-item -->
                <div class="select-menu-item js-navigation-item js-navigation-target ">
                  <span class="select-menu-item-icon mini-icon mini-icon-confirm"></span>
                  <a href="/mattpap/sympy/blob/pydy-pull-fixes/sympy/polys/benchmarks/bench_solvers.py" class="js-navigation-open select-menu-item-text js-select-button-text css-truncate-target" data-name="pydy-pull-fixes" rel="nofollow" title="pydy-pull-fixes">pydy-pull-fixes</a>
                </div> <!-- /.select-menu-item -->
                <div class="select-menu-item js-navigation-item js-navigation-target ">
                  <span class="select-menu-item-icon mini-icon mini-icon-confirm"></span>
                  <a href="/mattpap/sympy/blob/pypy-fixes/sympy/polys/benchmarks/bench_solvers.py" class="js-navigation-open select-menu-item-text js-select-button-text css-truncate-target" data-name="pypy-fixes" rel="nofollow" title="pypy-fixes">pypy-fixes</a>
                </div> <!-- /.select-menu-item -->
                <div class="select-menu-item js-navigation-item js-navigation-target ">
                  <span class="select-menu-item-icon mini-icon mini-icon-confirm"></span>
                  <a href="/mattpap/sympy/blob/python3-fixes/sympy/polys/benchmarks/bench_solvers.py" class="js-navigation-open select-menu-item-text js-select-button-text css-truncate-target" data-name="python3-fixes" rel="nofollow" title="python3-fixes">python3-fixes</a>
                </div> <!-- /.select-menu-item -->
                <div class="select-menu-item js-navigation-item js-navigation-target ">
                  <span class="select-menu-item-icon mini-icon mini-icon-confirm"></span>
                  <a href="/mattpap/sympy/blob/quiet_no_ipython/sympy/polys/benchmarks/bench_solvers.py" class="js-navigation-open select-menu-item-text js-select-button-text css-truncate-target" data-name="quiet_no_ipython" rel="nofollow" title="quiet_no_ipython">quiet_no_ipython</a>
                </div> <!-- /.select-menu-item -->
                <div class="select-menu-item js-navigation-item js-navigation-target ">
                  <span class="select-menu-item-icon mini-icon mini-icon-confirm"></span>
                  <a href="/mattpap/sympy/blob/rational_gcd/sympy/polys/benchmarks/bench_solvers.py" class="js-navigation-open select-menu-item-text js-select-button-text css-truncate-target" data-name="rational_gcd" rel="nofollow" title="rational_gcd">rational_gcd</a>
                </div> <!-- /.select-menu-item -->
                <div class="select-menu-item js-navigation-item js-navigation-target ">
                  <span class="select-menu-item-icon mini-icon mini-icon-confirm"></span>
                  <a href="/mattpap/sympy/blob/rational-inequalities/sympy/polys/benchmarks/bench_solvers.py" class="js-navigation-open select-menu-item-text js-select-button-text css-truncate-target" data-name="rational-inequalities" rel="nofollow" title="rational-inequalities">rational-inequalities</a>
                </div> <!-- /.select-menu-item -->
                <div class="select-menu-item js-navigation-item js-navigation-target ">
                  <span class="select-menu-item-icon mini-icon mini-icon-confirm"></span>
                  <a href="/mattpap/sympy/blob/real_domain/sympy/polys/benchmarks/bench_solvers.py" class="js-navigation-open select-menu-item-text js-select-button-text css-truncate-target" data-name="real_domain" rel="nofollow" title="real_domain">real_domain</a>
                </div> <!-- /.select-menu-item -->
                <div class="select-menu-item js-navigation-item js-navigation-target ">
                  <span class="select-menu-item-icon mini-icon mini-icon-confirm"></span>
                  <a href="/mattpap/sympy/blob/realfield/sympy/polys/benchmarks/bench_solvers.py" class="js-navigation-open select-menu-item-text js-select-button-text css-truncate-target" data-name="realfield" rel="nofollow" title="realfield">realfield</a>
                </div> <!-- /.select-menu-item -->
                <div class="select-menu-item js-navigation-item js-navigation-target ">
                  <span class="select-menu-item-icon mini-icon mini-icon-confirm"></span>
                  <a href="/mattpap/sympy/blob/reduced/sympy/polys/benchmarks/bench_solvers.py" class="js-navigation-open select-menu-item-text js-select-button-text css-truncate-target" data-name="reduced" rel="nofollow" title="reduced">reduced</a>
                </div> <!-- /.select-menu-item -->
                <div class="select-menu-item js-navigation-item js-navigation-target ">
                  <span class="select-menu-item-icon mini-icon mini-icon-confirm"></span>
                  <a href="/mattpap/sympy/blob/remove-keep-sign/sympy/polys/benchmarks/bench_solvers.py" class="js-navigation-open select-menu-item-text js-select-button-text css-truncate-target" data-name="remove-keep-sign" rel="nofollow" title="remove-keep-sign">remove-keep-sign</a>
                </div> <!-- /.select-menu-item -->
                <div class="select-menu-item js-navigation-item js-navigation-target ">
                  <span class="select-menu-item-icon mini-icon mini-icon-confirm"></span>
                  <a href="/mattpap/sympy/blob/rootof/sympy/polys/benchmarks/bench_solvers.py" class="js-navigation-open select-menu-item-text js-select-button-text css-truncate-target" data-name="rootof" rel="nofollow" title="rootof">rootof</a>
                </div> <!-- /.select-menu-item -->
                <div class="select-menu-item js-navigation-item js-navigation-target ">
                  <span class="select-menu-item-icon mini-icon mini-icon-confirm"></span>
                  <a href="/mattpap/sympy/blob/roots/sympy/polys/benchmarks/bench_solvers.py" class="js-navigation-open select-menu-item-text js-select-button-text css-truncate-target" data-name="roots" rel="nofollow" title="roots">roots</a>
                </div> <!-- /.select-menu-item -->
                <div class="select-menu-item js-navigation-item js-navigation-target ">
                  <span class="select-menu-item-icon mini-icon mini-icon-confirm"></span>
                  <a href="/mattpap/sympy/blob/runtests_exceptions/sympy/polys/benchmarks/bench_solvers.py" class="js-navigation-open select-menu-item-text js-select-button-text css-truncate-target" data-name="runtests_exceptions" rel="nofollow" title="runtests_exceptions">runtests_exceptions</a>
                </div> <!-- /.select-menu-item -->
                <div class="select-menu-item js-navigation-item js-navigation-target ">
                  <span class="select-menu-item-icon mini-icon mini-icon-confirm"></span>
                  <a href="/mattpap/sympy/blob/scipy-2011-tutorial/sympy/polys/benchmarks/bench_solvers.py" class="js-navigation-open select-menu-item-text js-select-button-text css-truncate-target" data-name="scipy-2011-tutorial" rel="nofollow" title="scipy-2011-tutorial">scipy-2011-tutorial</a>
                </div> <!-- /.select-menu-item -->
                <div class="select-menu-item js-navigation-item js-navigation-target ">
                  <span class="select-menu-item-icon mini-icon mini-icon-confirm"></span>
                  <a href="/mattpap/sympy/blob/solve/sympy/polys/benchmarks/bench_solvers.py" class="js-navigation-open select-menu-item-text js-select-button-text css-truncate-target" data-name="solve" rel="nofollow" title="solve">solve</a>
                </div> <!-- /.select-menu-item -->
                <div class="select-menu-item js-navigation-item js-navigation-target selected">
                  <span class="select-menu-item-icon mini-icon mini-icon-confirm"></span>
                  <a href="/mattpap/sympy/blob/sparse-polys/sympy/polys/benchmarks/bench_solvers.py" class="js-navigation-open select-menu-item-text js-select-button-text css-truncate-target" data-name="sparse-polys" rel="nofollow" title="sparse-polys">sparse-polys</a>
                </div> <!-- /.select-menu-item -->
                <div class="select-menu-item js-navigation-item js-navigation-target ">
                  <span class="select-menu-item-icon mini-icon mini-icon-confirm"></span>
                  <a href="/mattpap/sympy/blob/speedup/sympy/polys/benchmarks/bench_solvers.py" class="js-navigation-open select-menu-item-text js-select-button-text css-truncate-target" data-name="speedup" rel="nofollow" title="speedup">speedup</a>
                </div> <!-- /.select-menu-item -->
                <div class="select-menu-item js-navigation-item js-navigation-target ">
                  <span class="select-menu-item-icon mini-icon mini-icon-confirm"></span>
                  <a href="/mattpap/sympy/blob/term_width/sympy/polys/benchmarks/bench_solvers.py" class="js-navigation-open select-menu-item-text js-select-button-text css-truncate-target" data-name="term_width" rel="nofollow" title="term_width">term_width</a>
                </div> <!-- /.select-menu-item -->
                <div class="select-menu-item js-navigation-item js-navigation-target ">
                  <span class="select-menu-item-icon mini-icon mini-icon-confirm"></span>
                  <a href="/mattpap/sympy/blob/test_args_pyglet/sympy/polys/benchmarks/bench_solvers.py" class="js-navigation-open select-menu-item-text js-select-button-text css-truncate-target" data-name="test_args_pyglet" rel="nofollow" title="test_args_pyglet">test_args_pyglet</a>
                </div> <!-- /.select-menu-item -->
                <div class="select-menu-item js-navigation-item js-navigation-target ">
                  <span class="select-menu-item-icon mini-icon mini-icon-confirm"></span>
                  <a href="/mattpap/sympy/blob/test_issue604/sympy/polys/benchmarks/bench_solvers.py" class="js-navigation-open select-menu-item-text js-select-button-text css-truncate-target" data-name="test_issue604" rel="nofollow" title="test_issue604">test_issue604</a>
                </div> <!-- /.select-menu-item -->
                <div class="select-menu-item js-navigation-item js-navigation-target ">
                  <span class="select-menu-item-icon mini-icon mini-icon-confirm"></span>
                  <a href="/mattpap/sympy/blob/test_issue_1001/sympy/polys/benchmarks/bench_solvers.py" class="js-navigation-open select-menu-item-text js-select-button-text css-truncate-target" data-name="test_issue_1001" rel="nofollow" title="test_issue_1001">test_issue_1001</a>
                </div> <!-- /.select-menu-item -->
                <div class="select-menu-item js-navigation-item js-navigation-target ">
                  <span class="select-menu-item-icon mini-icon mini-icon-confirm"></span>
                  <a href="/mattpap/sympy/blob/tests/sympy/polys/benchmarks/bench_solvers.py" class="js-navigation-open select-menu-item-text js-select-button-text css-truncate-target" data-name="tests" rel="nofollow" title="tests">tests</a>
                </div> <!-- /.select-menu-item -->
                <div class="select-menu-item js-navigation-item js-navigation-target ">
                  <span class="select-menu-item-icon mini-icon mini-icon-confirm"></span>
                  <a href="/mattpap/sympy/blob/tsolve/sympy/polys/benchmarks/bench_solvers.py" class="js-navigation-open select-menu-item-text js-select-button-text css-truncate-target" data-name="tsolve" rel="nofollow" title="tsolve">tsolve</a>
                </div> <!-- /.select-menu-item -->
                <div class="select-menu-item js-navigation-item js-navigation-target ">
                  <span class="select-menu-item-icon mini-icon mini-icon-confirm"></span>
                  <a href="/mattpap/sympy/blob/unified-gcd/sympy/polys/benchmarks/bench_solvers.py" class="js-navigation-open select-menu-item-text js-select-button-text css-truncate-target" data-name="unified-gcd" rel="nofollow" title="unified-gcd">unified-gcd</a>
                </div> <!-- /.select-menu-item -->
                <div class="select-menu-item js-navigation-item js-navigation-target ">
                  <span class="select-menu-item-icon mini-icon mini-icon-confirm"></span>
                  <a href="/mattpap/sympy/blob/wikitest/sympy/polys/benchmarks/bench_solvers.py" class="js-navigation-open select-menu-item-text js-select-button-text css-truncate-target" data-name="wikitest" rel="nofollow" title="wikitest">wikitest</a>
                </div> <!-- /.select-menu-item -->
                <div class="select-menu-item js-navigation-item js-navigation-target ">
                  <span class="select-menu-item-icon mini-icon mini-icon-confirm"></span>
                  <a href="/mattpap/sympy/blob/zeros/sympy/polys/benchmarks/bench_solvers.py" class="js-navigation-open select-menu-item-text js-select-button-text css-truncate-target" data-name="zeros" rel="nofollow" title="zeros">zeros</a>
                </div> <!-- /.select-menu-item -->
            </div>

              <div class="select-menu-no-results">Nothing to show</div>
          </div> <!-- /.select-menu-list -->


          <div class="select-menu-list select-menu-tab-bucket js-select-menu-tab-bucket css-truncate" data-tab-filter="tags">
            <div data-filterable-for="commitish-filter-field" data-filterable-type="substring">

                <div class="select-menu-item js-navigation-item js-navigation-target ">
                  <span class="select-menu-item-icon mini-icon mini-icon-confirm"></span>
                  <a href="/mattpap/sympy/blob/sympy-0.6.7/sympy/polys/benchmarks/bench_solvers.py" class="js-navigation-open select-menu-item-text js-select-button-text css-truncate-target" data-name="sympy-0.6.7" rel="nofollow" title="sympy-0.6.7">sympy-0.6.7</a>
                </div> <!-- /.select-menu-item -->
                <div class="select-menu-item js-navigation-item js-navigation-target ">
                  <span class="select-menu-item-icon mini-icon mini-icon-confirm"></span>
                  <a href="/mattpap/sympy/blob/sympy-0.6.6.rc1/sympy/polys/benchmarks/bench_solvers.py" class="js-navigation-open select-menu-item-text js-select-button-text css-truncate-target" data-name="sympy-0.6.6.rc1" rel="nofollow" title="sympy-0.6.6.rc1">sympy-0.6.6.rc1</a>
                </div> <!-- /.select-menu-item -->
                <div class="select-menu-item js-navigation-item js-navigation-target ">
                  <span class="select-menu-item-icon mini-icon mini-icon-confirm"></span>
                  <a href="/mattpap/sympy/blob/sympy-0.6.6/sympy/polys/benchmarks/bench_solvers.py" class="js-navigation-open select-menu-item-text js-select-button-text css-truncate-target" data-name="sympy-0.6.6" rel="nofollow" title="sympy-0.6.6">sympy-0.6.6</a>
                </div> <!-- /.select-menu-item -->
                <div class="select-menu-item js-navigation-item js-navigation-target ">
                  <span class="select-menu-item-icon mini-icon mini-icon-confirm"></span>
                  <a href="/mattpap/sympy/blob/sympy-0.6.5.rc2/sympy/polys/benchmarks/bench_solvers.py" class="js-navigation-open select-menu-item-text js-select-button-text css-truncate-target" data-name="sympy-0.6.5.rc2" rel="nofollow" title="sympy-0.6.5.rc2">sympy-0.6.5.rc2</a>
                </div> <!-- /.select-menu-item -->
                <div class="select-menu-item js-navigation-item js-navigation-target ">
                  <span class="select-menu-item-icon mini-icon mini-icon-confirm"></span>
                  <a href="/mattpap/sympy/blob/sympy-0.6.5.rc1/sympy/polys/benchmarks/bench_solvers.py" class="js-navigation-open select-menu-item-text js-select-button-text css-truncate-target" data-name="sympy-0.6.5.rc1" rel="nofollow" title="sympy-0.6.5.rc1">sympy-0.6.5.rc1</a>
                </div> <!-- /.select-menu-item -->
                <div class="select-menu-item js-navigation-item js-navigation-target ">
                  <span class="select-menu-item-icon mini-icon mini-icon-confirm"></span>
                  <a href="/mattpap/sympy/blob/sympy-0.6.5.beta3/sympy/polys/benchmarks/bench_solvers.py" class="js-navigation-open select-menu-item-text js-select-button-text css-truncate-target" data-name="sympy-0.6.5.beta3" rel="nofollow" title="sympy-0.6.5.beta3">sympy-0.6.5.beta3</a>
                </div> <!-- /.select-menu-item -->
                <div class="select-menu-item js-navigation-item js-navigation-target ">
                  <span class="select-menu-item-icon mini-icon mini-icon-confirm"></span>
                  <a href="/mattpap/sympy/blob/sympy-0.6.5.beta2/sympy/polys/benchmarks/bench_solvers.py" class="js-navigation-open select-menu-item-text js-select-button-text css-truncate-target" data-name="sympy-0.6.5.beta2" rel="nofollow" title="sympy-0.6.5.beta2">sympy-0.6.5.beta2</a>
                </div> <!-- /.select-menu-item -->
                <div class="select-menu-item js-navigation-item js-navigation-target ">
                  <span class="select-menu-item-icon mini-icon mini-icon-confirm"></span>
                  <a href="/mattpap/sympy/blob/sympy-0.6.5-beta1/sympy/polys/benchmarks/bench_solvers.py" class="js-navigation-open select-menu-item-text js-select-button-text css-truncate-target" data-name="sympy-0.6.5-beta1" rel="nofollow" title="sympy-0.6.5-beta1">sympy-0.6.5-beta1</a>
                </div> <!-- /.select-menu-item -->
                <div class="select-menu-item js-navigation-item js-navigation-target ">
                  <span class="select-menu-item-icon mini-icon mini-icon-confirm"></span>
                  <a href="/mattpap/sympy/blob/sympy-0.6.5/sympy/polys/benchmarks/bench_solvers.py" class="js-navigation-open select-menu-item-text js-select-button-text css-truncate-target" data-name="sympy-0.6.5" rel="nofollow" title="sympy-0.6.5">sympy-0.6.5</a>
                </div> <!-- /.select-menu-item -->
                <div class="select-menu-item js-navigation-item js-navigation-target ">
                  <span class="select-menu-item-icon mini-icon mini-icon-confirm"></span>
                  <a href="/mattpap/sympy/blob/sympy-0.6.4.beta3/sympy/polys/benchmarks/bench_solvers.py" class="js-navigation-open select-menu-item-text js-select-button-text css-truncate-target" data-name="sympy-0.6.4.beta3" rel="nofollow" title="sympy-0.6.4.beta3">sympy-0.6.4.beta3</a>
                </div> <!-- /.select-menu-item -->
                <div class="select-menu-item js-navigation-item js-navigation-target ">
                  <span class="select-menu-item-icon mini-icon mini-icon-confirm"></span>
                  <a href="/mattpap/sympy/blob/sympy-0.6.4.beta2/sympy/polys/benchmarks/bench_solvers.py" class="js-navigation-open select-menu-item-text js-select-button-text css-truncate-target" data-name="sympy-0.6.4.beta2" rel="nofollow" title="sympy-0.6.4.beta2">sympy-0.6.4.beta2</a>
                </div> <!-- /.select-menu-item -->
                <div class="select-menu-item js-navigation-item js-navigation-target ">
                  <span class="select-menu-item-icon mini-icon mini-icon-confirm"></span>
                  <a href="/mattpap/sympy/blob/sympy-0.6.4.beta1/sympy/polys/benchmarks/bench_solvers.py" class="js-navigation-open select-menu-item-text js-select-button-text css-truncate-target" data-name="sympy-0.6.4.beta1" rel="nofollow" title="sympy-0.6.4.beta1">sympy-0.6.4.beta1</a>
                </div> <!-- /.select-menu-item -->
                <div class="select-menu-item js-navigation-item js-navigation-target ">
                  <span class="select-menu-item-icon mini-icon mini-icon-confirm"></span>
                  <a href="/mattpap/sympy/blob/sympy-0.6.4/sympy/polys/benchmarks/bench_solvers.py" class="js-navigation-open select-menu-item-text js-select-button-text css-truncate-target" data-name="sympy-0.6.4" rel="nofollow" title="sympy-0.6.4">sympy-0.6.4</a>
                </div> <!-- /.select-menu-item -->
                <div class="select-menu-item js-navigation-item js-navigation-target ">
                  <span class="select-menu-item-icon mini-icon mini-icon-confirm"></span>
                  <a href="/mattpap/sympy/blob/sympy-0.6.3.beta2/sympy/polys/benchmarks/bench_solvers.py" class="js-navigation-open select-menu-item-text js-select-button-text css-truncate-target" data-name="sympy-0.6.3.beta2" rel="nofollow" title="sympy-0.6.3.beta2">sympy-0.6.3.beta2</a>
                </div> <!-- /.select-menu-item -->
                <div class="select-menu-item js-navigation-item js-navigation-target ">
                  <span class="select-menu-item-icon mini-icon mini-icon-confirm"></span>
                  <a href="/mattpap/sympy/blob/sympy-0.6.3.beta1/sympy/polys/benchmarks/bench_solvers.py" class="js-navigation-open select-menu-item-text js-select-button-text css-truncate-target" data-name="sympy-0.6.3.beta1" rel="nofollow" title="sympy-0.6.3.beta1">sympy-0.6.3.beta1</a>
                </div> <!-- /.select-menu-item -->
                <div class="select-menu-item js-navigation-item js-navigation-target ">
                  <span class="select-menu-item-icon mini-icon mini-icon-confirm"></span>
                  <a href="/mattpap/sympy/blob/sympy-0.6.3/sympy/polys/benchmarks/bench_solvers.py" class="js-navigation-open select-menu-item-text js-select-button-text css-truncate-target" data-name="sympy-0.6.3" rel="nofollow" title="sympy-0.6.3">sympy-0.6.3</a>
                </div> <!-- /.select-menu-item -->
                <div class="select-menu-item js-navigation-item js-navigation-target ">
                  <span class="select-menu-item-icon mini-icon mini-icon-confirm"></span>
                  <a href="/mattpap/sympy/blob/sympy-0.6.2/sympy/polys/benchmarks/bench_solvers.py" class="js-navigation-open select-menu-item-text js-select-button-text css-truncate-target" data-name="sympy-0.6.2" rel="nofollow" title="sympy-0.6.2">sympy-0.6.2</a>
                </div> <!-- /.select-menu-item -->
                <div class="select-menu-item js-navigation-item js-navigation-target ">
                  <span class="select-menu-item-icon mini-icon mini-icon-confirm"></span>
                  <a href="/mattpap/sympy/blob/sympy-0.6.1/sympy/polys/benchmarks/bench_solvers.py" class="js-navigation-open select-menu-item-text js-select-button-text css-truncate-target" data-name="sympy-0.6.1" rel="nofollow" title="sympy-0.6.1">sympy-0.6.1</a>
                </div> <!-- /.select-menu-item -->
                <div class="select-menu-item js-navigation-item js-navigation-target ">
                  <span class="select-menu-item-icon mini-icon mini-icon-confirm"></span>
                  <a href="/mattpap/sympy/blob/sympy-0.6.0/sympy/polys/benchmarks/bench_solvers.py" class="js-navigation-open select-menu-item-text js-select-button-text css-truncate-target" data-name="sympy-0.6.0" rel="nofollow" title="sympy-0.6.0">sympy-0.6.0</a>
                </div> <!-- /.select-menu-item -->
                <div class="select-menu-item js-navigation-item js-navigation-target ">
                  <span class="select-menu-item-icon mini-icon mini-icon-confirm"></span>
                  <a href="/mattpap/sympy/blob/sympy-0.5.15/sympy/polys/benchmarks/bench_solvers.py" class="js-navigation-open select-menu-item-text js-select-button-text css-truncate-target" data-name="sympy-0.5.15" rel="nofollow" title="sympy-0.5.15">sympy-0.5.15</a>
                </div> <!-- /.select-menu-item -->
                <div class="select-menu-item js-navigation-item js-navigation-target ">
                  <span class="select-menu-item-icon mini-icon mini-icon-confirm"></span>
                  <a href="/mattpap/sympy/blob/sympy-0.5.14/sympy/polys/benchmarks/bench_solvers.py" class="js-navigation-open select-menu-item-text js-select-button-text css-truncate-target" data-name="sympy-0.5.14" rel="nofollow" title="sympy-0.5.14">sympy-0.5.14</a>
                </div> <!-- /.select-menu-item -->
                <div class="select-menu-item js-navigation-item js-navigation-target ">
                  <span class="select-menu-item-icon mini-icon mini-icon-confirm"></span>
                  <a href="/mattpap/sympy/blob/sympy-0.5.13/sympy/polys/benchmarks/bench_solvers.py" class="js-navigation-open select-menu-item-text js-select-button-text css-truncate-target" data-name="sympy-0.5.13" rel="nofollow" title="sympy-0.5.13">sympy-0.5.13</a>
                </div> <!-- /.select-menu-item -->
                <div class="select-menu-item js-navigation-item js-navigation-target ">
                  <span class="select-menu-item-icon mini-icon mini-icon-confirm"></span>
                  <a href="/mattpap/sympy/blob/sympy-0.5.12/sympy/polys/benchmarks/bench_solvers.py" class="js-navigation-open select-menu-item-text js-select-button-text css-truncate-target" data-name="sympy-0.5.12" rel="nofollow" title="sympy-0.5.12">sympy-0.5.12</a>
                </div> <!-- /.select-menu-item -->
                <div class="select-menu-item js-navigation-item js-navigation-target ">
                  <span class="select-menu-item-icon mini-icon mini-icon-confirm"></span>
                  <a href="/mattpap/sympy/blob/sympy-0.5.11/sympy/polys/benchmarks/bench_solvers.py" class="js-navigation-open select-menu-item-text js-select-button-text css-truncate-target" data-name="sympy-0.5.11" rel="nofollow" title="sympy-0.5.11">sympy-0.5.11</a>
                </div> <!-- /.select-menu-item -->
                <div class="select-menu-item js-navigation-item js-navigation-target ">
                  <span class="select-menu-item-icon mini-icon mini-icon-confirm"></span>
                  <a href="/mattpap/sympy/blob/sympy-0.5.10/sympy/polys/benchmarks/bench_solvers.py" class="js-navigation-open select-menu-item-text js-select-button-text css-truncate-target" data-name="sympy-0.5.10" rel="nofollow" title="sympy-0.5.10">sympy-0.5.10</a>
                </div> <!-- /.select-menu-item -->
                <div class="select-menu-item js-navigation-item js-navigation-target ">
                  <span class="select-menu-item-icon mini-icon mini-icon-confirm"></span>
                  <a href="/mattpap/sympy/blob/sympy-0.5.9/sympy/polys/benchmarks/bench_solvers.py" class="js-navigation-open select-menu-item-text js-select-button-text css-truncate-target" data-name="sympy-0.5.9" rel="nofollow" title="sympy-0.5.9">sympy-0.5.9</a>
                </div> <!-- /.select-menu-item -->
                <div class="select-menu-item js-navigation-item js-navigation-target ">
                  <span class="select-menu-item-icon mini-icon mini-icon-confirm"></span>
                  <a href="/mattpap/sympy/blob/sympy-0.5.8/sympy/polys/benchmarks/bench_solvers.py" class="js-navigation-open select-menu-item-text js-select-button-text css-truncate-target" data-name="sympy-0.5.8" rel="nofollow" title="sympy-0.5.8">sympy-0.5.8</a>
                </div> <!-- /.select-menu-item -->
                <div class="select-menu-item js-navigation-item js-navigation-target ">
                  <span class="select-menu-item-icon mini-icon mini-icon-confirm"></span>
                  <a href="/mattpap/sympy/blob/sympy-0.5.7/sympy/polys/benchmarks/bench_solvers.py" class="js-navigation-open select-menu-item-text js-select-button-text css-truncate-target" data-name="sympy-0.5.7" rel="nofollow" title="sympy-0.5.7">sympy-0.5.7</a>
                </div> <!-- /.select-menu-item -->
                <div class="select-menu-item js-navigation-item js-navigation-target ">
                  <span class="select-menu-item-icon mini-icon mini-icon-confirm"></span>
                  <a href="/mattpap/sympy/blob/sympy-0.5.6/sympy/polys/benchmarks/bench_solvers.py" class="js-navigation-open select-menu-item-text js-select-button-text css-truncate-target" data-name="sympy-0.5.6" rel="nofollow" title="sympy-0.5.6">sympy-0.5.6</a>
                </div> <!-- /.select-menu-item -->
                <div class="select-menu-item js-navigation-item js-navigation-target ">
                  <span class="select-menu-item-icon mini-icon mini-icon-confirm"></span>
                  <a href="/mattpap/sympy/blob/sympy-0.5.5/sympy/polys/benchmarks/bench_solvers.py" class="js-navigation-open select-menu-item-text js-select-button-text css-truncate-target" data-name="sympy-0.5.5" rel="nofollow" title="sympy-0.5.5">sympy-0.5.5</a>
                </div> <!-- /.select-menu-item -->
                <div class="select-menu-item js-navigation-item js-navigation-target ">
                  <span class="select-menu-item-icon mini-icon mini-icon-confirm"></span>
                  <a href="/mattpap/sympy/blob/sympy-0.5.4/sympy/polys/benchmarks/bench_solvers.py" class="js-navigation-open select-menu-item-text js-select-button-text css-truncate-target" data-name="sympy-0.5.4" rel="nofollow" title="sympy-0.5.4">sympy-0.5.4</a>
                </div> <!-- /.select-menu-item -->
                <div class="select-menu-item js-navigation-item js-navigation-target ">
                  <span class="select-menu-item-icon mini-icon mini-icon-confirm"></span>
                  <a href="/mattpap/sympy/blob/sympy-0.5.3/sympy/polys/benchmarks/bench_solvers.py" class="js-navigation-open select-menu-item-text js-select-button-text css-truncate-target" data-name="sympy-0.5.3" rel="nofollow" title="sympy-0.5.3">sympy-0.5.3</a>
                </div> <!-- /.select-menu-item -->
                <div class="select-menu-item js-navigation-item js-navigation-target ">
                  <span class="select-menu-item-icon mini-icon mini-icon-confirm"></span>
                  <a href="/mattpap/sympy/blob/sympy-0.5.0/sympy/polys/benchmarks/bench_solvers.py" class="js-navigation-open select-menu-item-text js-select-button-text css-truncate-target" data-name="sympy-0.5.0" rel="nofollow" title="sympy-0.5.0">sympy-0.5.0</a>
                </div> <!-- /.select-menu-item -->
            </div>

            <div class="select-menu-no-results">Nothing to show</div>

          </div> <!-- /.select-menu-list -->

        </div> <!-- /.select-menu-modal -->
      </div> <!-- /.select-menu-modal-holder -->
    </div> <!-- /.select-menu -->

  </div> <!-- /.scope -->

  <ul class="tabnav-tabs">
    <li><a href="/mattpap/sympy/tree/sparse-polys" class="selected tabnav-tab" highlight="repo_source">Files</a></li>
    <li><a href="/mattpap/sympy/commits/sparse-polys" class="tabnav-tab" highlight="repo_commits">Commits</a></li>
    <li><a href="/mattpap/sympy/branches" class="tabnav-tab" highlight="repo_branches" rel="nofollow">Branches <span class="counter ">88</span></a></li>
  </ul>

</div>

  
  
  


            
          </div>
        </div><!-- /.repohead -->

        <div id="js-repo-pjax-container" class="container context-loader-container" data-pjax-container>
          


<!-- blob contrib key: blob_contributors:v21:f8ce2853b48adc8f3cd02dde8ad344f8 -->
<!-- blob contrib frag key: views10/v8/blob_contributors:v21:f8ce2853b48adc8f3cd02dde8ad344f8 -->


<div id="slider">
    <div class="frame-meta">

      <p title="This is a placeholder element" class="js-history-link-replace hidden"></p>

        <div class="breadcrumb">
          <span class='bold'><span itemscope="" itemtype="http://data-vocabulary.org/Breadcrumb"><a href="/mattpap/sympy/tree/sparse-polys" class="js-slide-to" data-branch="sparse-polys" data-direction="back" itemscope="url"><span itemprop="title">sympy</span></a></span></span><span class="separator"> / </span><span itemscope="" itemtype="http://data-vocabulary.org/Breadcrumb"><a href="/mattpap/sympy/tree/sparse-polys/sympy" class="js-slide-to" data-branch="sparse-polys" data-direction="back" itemscope="url"><span itemprop="title">sympy</span></a></span><span class="separator"> / </span><span itemscope="" itemtype="http://data-vocabulary.org/Breadcrumb"><a href="/mattpap/sympy/tree/sparse-polys/sympy/polys" class="js-slide-to" data-branch="sparse-polys" data-direction="back" itemscope="url"><span itemprop="title">polys</span></a></span><span class="separator"> / </span><span itemscope="" itemtype="http://data-vocabulary.org/Breadcrumb"><a href="/mattpap/sympy/tree/sparse-polys/sympy/polys/benchmarks" class="js-slide-to" data-branch="sparse-polys" data-direction="back" itemscope="url"><span itemprop="title">benchmarks</span></a></span><span class="separator"> / </span><strong class="final-path">bench_solvers.py</strong> <span class="js-zeroclipboard zeroclipboard-button" data-clipboard-text="sympy/polys/benchmarks/bench_solvers.py" data-copied-hint="copied!" title="copy to clipboard"><span class="mini-icon mini-icon-clipboard"></span></span>
        </div>

      <a href="/mattpap/sympy/find/sparse-polys" class="js-slide-to" data-hotkey="t" style="display:none">Show File Finder</a>


        
  <div class="commit file-history-tease">
    <img class="main-avatar" height="24" src="https://secure.gravatar.com/avatar/89164142ec718a76a7e04481062acaea?s=140&amp;d=https://a248.e.akamai.net/assets.github.com%2Fimages%2Fgravatars%2Fgravatar-user-420.png" width="24" />
    <span class="author"><a href="/mattpap" rel="author">mattpap</a></span>
    <time class="js-relative-date" datetime="2013-03-18T15:17:54-07:00" title="2013-03-18 15:17:54">March 18, 2013</time>
    <div class="commit-title">
        <a href="/mattpap/sympy/commit/5f884fa217b5bad3a31bca1a72ef3efb727d9bf4" class="message">polys: Added support for FracElement.from_expr(Rational(p, q))</a>
    </div>

    <div class="participation">
      <p class="quickstat"><a href="#blob_contributors_box" rel="facebox"><strong>1</strong> contributor</a></p>
      
    </div>
    <div id="blob_contributors_box" style="display:none">
      <h2>Users on GitHub who have contributed to this file</h2>
      <ul class="facebox-user-list">
        <li>
          <img height="24" src="https://secure.gravatar.com/avatar/89164142ec718a76a7e04481062acaea?s=140&amp;d=https://a248.e.akamai.net/assets.github.com%2Fimages%2Fgravatars%2Fgravatar-user-420.png" width="24" />
          <a href="/mattpap">mattpap</a>
        </li>
      </ul>
    </div>
  </div>


    </div><!-- ./.frame-meta -->

    <div class="frames">
      <div class="frame" data-permalink-url="/mattpap/sympy/blob/aeb4c3684a22cb314b014fc92d9ea9b4b257ee2f/sympy/polys/benchmarks/bench_solvers.py" data-title="sympy/sympy/polys/benchmarks/bench_solvers.py at sparse-polys · mattpap/sympy · GitHub" data-type="blob">

        <div id="files" class="bubble">
          <div class="file">
            <div class="meta">
              <div class="info">
                <span class="icon"><b class="mini-icon mini-icon-text-file"></b></span>
                <span class="mode" title="File Mode">file</span>
                  <span>247 lines (239 sloc)</span>
                <span>434.661 kb</span>
              </div>
              <div class="actions">
                <div class="button-group">
                      <a class="minibutton js-entice" href=""
                         data-entice="You must be signed in and on a branch to make or propose changes">Edit</a>
                  <a href="/mattpap/sympy/raw/sparse-polys/sympy/polys/benchmarks/bench_solvers.py" class="button minibutton " id="raw-url">Raw</a>
                    <a href="/mattpap/sympy/blame/sparse-polys/sympy/polys/benchmarks/bench_solvers.py" class="button minibutton ">Blame</a>
                  <a href="/mattpap/sympy/commits/sparse-polys/sympy/polys/benchmarks/bench_solvers.py" class="button minibutton " rel="nofollow">History</a>
                </div><!-- /.button-group -->
              </div><!-- /.actions -->

            </div>
                <div class="data type-python js-blob-data">
      <table cellpadding="0" cellspacing="0" class="lines">
        <tr>
          <td>
            <pre class="line_numbers"><span id="L1" rel="#L1">1</span>
<span id="L2" rel="#L2">2</span>
<span id="L3" rel="#L3">3</span>
<span id="L4" rel="#L4">4</span>
<span id="L5" rel="#L5">5</span>
<span id="L6" rel="#L6">6</span>
<span id="L7" rel="#L7">7</span>
<span id="L8" rel="#L8">8</span>
<span id="L9" rel="#L9">9</span>
<span id="L10" rel="#L10">10</span>
<span id="L11" rel="#L11">11</span>
<span id="L12" rel="#L12">12</span>
<span id="L13" rel="#L13">13</span>
<span id="L14" rel="#L14">14</span>
<span id="L15" rel="#L15">15</span>
<span id="L16" rel="#L16">16</span>
<span id="L17" rel="#L17">17</span>
<span id="L18" rel="#L18">18</span>
<span id="L19" rel="#L19">19</span>
<span id="L20" rel="#L20">20</span>
<span id="L21" rel="#L21">21</span>
<span id="L22" rel="#L22">22</span>
<span id="L23" rel="#L23">23</span>
<span id="L24" rel="#L24">24</span>
<span id="L25" rel="#L25">25</span>
<span id="L26" rel="#L26">26</span>
<span id="L27" rel="#L27">27</span>
<span id="L28" rel="#L28">28</span>
<span id="L29" rel="#L29">29</span>
<span id="L30" rel="#L30">30</span>
<span id="L31" rel="#L31">31</span>
<span id="L32" rel="#L32">32</span>
<span id="L33" rel="#L33">33</span>
<span id="L34" rel="#L34">34</span>
<span id="L35" rel="#L35">35</span>
<span id="L36" rel="#L36">36</span>
<span id="L37" rel="#L37">37</span>
<span id="L38" rel="#L38">38</span>
<span id="L39" rel="#L39">39</span>
<span id="L40" rel="#L40">40</span>
<span id="L41" rel="#L41">41</span>
<span id="L42" rel="#L42">42</span>
<span id="L43" rel="#L43">43</span>
<span id="L44" rel="#L44">44</span>
<span id="L45" rel="#L45">45</span>
<span id="L46" rel="#L46">46</span>
<span id="L47" rel="#L47">47</span>
<span id="L48" rel="#L48">48</span>
<span id="L49" rel="#L49">49</span>
<span id="L50" rel="#L50">50</span>
<span id="L51" rel="#L51">51</span>
<span id="L52" rel="#L52">52</span>
<span id="L53" rel="#L53">53</span>
<span id="L54" rel="#L54">54</span>
<span id="L55" rel="#L55">55</span>
<span id="L56" rel="#L56">56</span>
<span id="L57" rel="#L57">57</span>
<span id="L58" rel="#L58">58</span>
<span id="L59" rel="#L59">59</span>
<span id="L60" rel="#L60">60</span>
<span id="L61" rel="#L61">61</span>
<span id="L62" rel="#L62">62</span>
<span id="L63" rel="#L63">63</span>
<span id="L64" rel="#L64">64</span>
<span id="L65" rel="#L65">65</span>
<span id="L66" rel="#L66">66</span>
<span id="L67" rel="#L67">67</span>
<span id="L68" rel="#L68">68</span>
<span id="L69" rel="#L69">69</span>
<span id="L70" rel="#L70">70</span>
<span id="L71" rel="#L71">71</span>
<span id="L72" rel="#L72">72</span>
<span id="L73" rel="#L73">73</span>
<span id="L74" rel="#L74">74</span>
<span id="L75" rel="#L75">75</span>
<span id="L76" rel="#L76">76</span>
<span id="L77" rel="#L77">77</span>
<span id="L78" rel="#L78">78</span>
<span id="L79" rel="#L79">79</span>
<span id="L80" rel="#L80">80</span>
<span id="L81" rel="#L81">81</span>
<span id="L82" rel="#L82">82</span>
<span id="L83" rel="#L83">83</span>
<span id="L84" rel="#L84">84</span>
<span id="L85" rel="#L85">85</span>
<span id="L86" rel="#L86">86</span>
<span id="L87" rel="#L87">87</span>
<span id="L88" rel="#L88">88</span>
<span id="L89" rel="#L89">89</span>
<span id="L90" rel="#L90">90</span>
<span id="L91" rel="#L91">91</span>
<span id="L92" rel="#L92">92</span>
<span id="L93" rel="#L93">93</span>
<span id="L94" rel="#L94">94</span>
<span id="L95" rel="#L95">95</span>
<span id="L96" rel="#L96">96</span>
<span id="L97" rel="#L97">97</span>
<span id="L98" rel="#L98">98</span>
<span id="L99" rel="#L99">99</span>
<span id="L100" rel="#L100">100</span>
<span id="L101" rel="#L101">101</span>
<span id="L102" rel="#L102">102</span>
<span id="L103" rel="#L103">103</span>
<span id="L104" rel="#L104">104</span>
<span id="L105" rel="#L105">105</span>
<span id="L106" rel="#L106">106</span>
<span id="L107" rel="#L107">107</span>
<span id="L108" rel="#L108">108</span>
<span id="L109" rel="#L109">109</span>
<span id="L110" rel="#L110">110</span>
<span id="L111" rel="#L111">111</span>
<span id="L112" rel="#L112">112</span>
<span id="L113" rel="#L113">113</span>
<span id="L114" rel="#L114">114</span>
<span id="L115" rel="#L115">115</span>
<span id="L116" rel="#L116">116</span>
<span id="L117" rel="#L117">117</span>
<span id="L118" rel="#L118">118</span>
<span id="L119" rel="#L119">119</span>
<span id="L120" rel="#L120">120</span>
<span id="L121" rel="#L121">121</span>
<span id="L122" rel="#L122">122</span>
<span id="L123" rel="#L123">123</span>
<span id="L124" rel="#L124">124</span>
<span id="L125" rel="#L125">125</span>
<span id="L126" rel="#L126">126</span>
<span id="L127" rel="#L127">127</span>
<span id="L128" rel="#L128">128</span>
<span id="L129" rel="#L129">129</span>
<span id="L130" rel="#L130">130</span>
<span id="L131" rel="#L131">131</span>
<span id="L132" rel="#L132">132</span>
<span id="L133" rel="#L133">133</span>
<span id="L134" rel="#L134">134</span>
<span id="L135" rel="#L135">135</span>
<span id="L136" rel="#L136">136</span>
<span id="L137" rel="#L137">137</span>
<span id="L138" rel="#L138">138</span>
<span id="L139" rel="#L139">139</span>
<span id="L140" rel="#L140">140</span>
<span id="L141" rel="#L141">141</span>
<span id="L142" rel="#L142">142</span>
<span id="L143" rel="#L143">143</span>
<span id="L144" rel="#L144">144</span>
<span id="L145" rel="#L145">145</span>
<span id="L146" rel="#L146">146</span>
<span id="L147" rel="#L147">147</span>
<span id="L148" rel="#L148">148</span>
<span id="L149" rel="#L149">149</span>
<span id="L150" rel="#L150">150</span>
<span id="L151" rel="#L151">151</span>
<span id="L152" rel="#L152">152</span>
<span id="L153" rel="#L153">153</span>
<span id="L154" rel="#L154">154</span>
<span id="L155" rel="#L155">155</span>
<span id="L156" rel="#L156">156</span>
<span id="L157" rel="#L157">157</span>
<span id="L158" rel="#L158">158</span>
<span id="L159" rel="#L159">159</span>
<span id="L160" rel="#L160">160</span>
<span id="L161" rel="#L161">161</span>
<span id="L162" rel="#L162">162</span>
<span id="L163" rel="#L163">163</span>
<span id="L164" rel="#L164">164</span>
<span id="L165" rel="#L165">165</span>
<span id="L166" rel="#L166">166</span>
<span id="L167" rel="#L167">167</span>
<span id="L168" rel="#L168">168</span>
<span id="L169" rel="#L169">169</span>
<span id="L170" rel="#L170">170</span>
<span id="L171" rel="#L171">171</span>
<span id="L172" rel="#L172">172</span>
<span id="L173" rel="#L173">173</span>
<span id="L174" rel="#L174">174</span>
<span id="L175" rel="#L175">175</span>
<span id="L176" rel="#L176">176</span>
<span id="L177" rel="#L177">177</span>
<span id="L178" rel="#L178">178</span>
<span id="L179" rel="#L179">179</span>
<span id="L180" rel="#L180">180</span>
<span id="L181" rel="#L181">181</span>
<span id="L182" rel="#L182">182</span>
<span id="L183" rel="#L183">183</span>
<span id="L184" rel="#L184">184</span>
<span id="L185" rel="#L185">185</span>
<span id="L186" rel="#L186">186</span>
<span id="L187" rel="#L187">187</span>
<span id="L188" rel="#L188">188</span>
<span id="L189" rel="#L189">189</span>
<span id="L190" rel="#L190">190</span>
<span id="L191" rel="#L191">191</span>
<span id="L192" rel="#L192">192</span>
<span id="L193" rel="#L193">193</span>
<span id="L194" rel="#L194">194</span>
<span id="L195" rel="#L195">195</span>
<span id="L196" rel="#L196">196</span>
<span id="L197" rel="#L197">197</span>
<span id="L198" rel="#L198">198</span>
<span id="L199" rel="#L199">199</span>
<span id="L200" rel="#L200">200</span>
<span id="L201" rel="#L201">201</span>
<span id="L202" rel="#L202">202</span>
<span id="L203" rel="#L203">203</span>
<span id="L204" rel="#L204">204</span>
<span id="L205" rel="#L205">205</span>
<span id="L206" rel="#L206">206</span>
<span id="L207" rel="#L207">207</span>
<span id="L208" rel="#L208">208</span>
<span id="L209" rel="#L209">209</span>
<span id="L210" rel="#L210">210</span>
<span id="L211" rel="#L211">211</span>
<span id="L212" rel="#L212">212</span>
<span id="L213" rel="#L213">213</span>
<span id="L214" rel="#L214">214</span>
<span id="L215" rel="#L215">215</span>
<span id="L216" rel="#L216">216</span>
<span id="L217" rel="#L217">217</span>
<span id="L218" rel="#L218">218</span>
<span id="L219" rel="#L219">219</span>
<span id="L220" rel="#L220">220</span>
<span id="L221" rel="#L221">221</span>
<span id="L222" rel="#L222">222</span>
<span id="L223" rel="#L223">223</span>
<span id="L224" rel="#L224">224</span>
<span id="L225" rel="#L225">225</span>
<span id="L226" rel="#L226">226</span>
<span id="L227" rel="#L227">227</span>
<span id="L228" rel="#L228">228</span>
<span id="L229" rel="#L229">229</span>
<span id="L230" rel="#L230">230</span>
<span id="L231" rel="#L231">231</span>
<span id="L232" rel="#L232">232</span>
<span id="L233" rel="#L233">233</span>
<span id="L234" rel="#L234">234</span>
<span id="L235" rel="#L235">235</span>
<span id="L236" rel="#L236">236</span>
<span id="L237" rel="#L237">237</span>
<span id="L238" rel="#L238">238</span>
<span id="L239" rel="#L239">239</span>
<span id="L240" rel="#L240">240</span>
<span id="L241" rel="#L241">241</span>
<span id="L242" rel="#L242">242</span>
<span id="L243" rel="#L243">243</span>
<span id="L244" rel="#L244">244</span>
<span id="L245" rel="#L245">245</span>
<span id="L246" rel="#L246">246</span>
</pre>
          </td>
          <td width="100%">