(function() {var implementors = {};
implementors["env_logger"] = [{"text":"impl Log for Logger","synthetic":false,"types":[]}];
implementors["log"] = [];
implementors["simplelog"] = [{"text":"impl Log for CombinedLogger","synthetic":false,"types":[]},{"text":"impl Log for SimpleLogger","synthetic":false,"types":[]},{"text":"impl Log for TermLogger","synthetic":false,"types":[]},{"text":"impl&lt;W:&nbsp;Write + Send + 'static&gt; Log for WriteLogger&lt;W&gt;","synthetic":false,"types":[]}];
if (window.register_implementors) {window.register_implementors(implementors);} else {window.pending_implementors = implementors;}})()