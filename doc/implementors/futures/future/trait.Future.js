(function() {var implementors = {};
implementors["futures"] = [];
implementors["tokio_io"] = [{"text":"impl&lt;R, W&gt; <a class=\"trait\" href=\"futures/future/trait.Future.html\" title=\"trait futures::future::Future\">Future</a> for <a class=\"struct\" href=\"tokio_io/io/struct.Copy.html\" title=\"struct tokio_io::io::Copy\">Copy</a>&lt;R, W&gt; <span class=\"where fmt-newline\">where<br>&nbsp;&nbsp;&nbsp;&nbsp;R: <a class=\"trait\" href=\"tokio_io/trait.AsyncRead.html\" title=\"trait tokio_io::AsyncRead\">AsyncRead</a>,<br>&nbsp;&nbsp;&nbsp;&nbsp;W: <a class=\"trait\" href=\"tokio_io/trait.AsyncWrite.html\" title=\"trait tokio_io::AsyncWrite\">AsyncWrite</a>,&nbsp;</span>","synthetic":false,"types":["tokio_io::io::copy::Copy"]},{"text":"impl&lt;A&gt; <a class=\"trait\" href=\"futures/future/trait.Future.html\" title=\"trait futures::future::Future\">Future</a> for <a class=\"struct\" href=\"tokio_io/io/struct.Flush.html\" title=\"struct tokio_io::io::Flush\">Flush</a>&lt;A&gt; <span class=\"where fmt-newline\">where<br>&nbsp;&nbsp;&nbsp;&nbsp;A: <a class=\"trait\" href=\"tokio_io/trait.AsyncWrite.html\" title=\"trait tokio_io::AsyncWrite\">AsyncWrite</a>,&nbsp;</span>","synthetic":false,"types":["tokio_io::io::flush::Flush"]},{"text":"impl&lt;R, T&gt; <a class=\"trait\" href=\"futures/future/trait.Future.html\" title=\"trait futures::future::Future\">Future</a> for <a class=\"struct\" href=\"tokio_io/io/struct.Read.html\" title=\"struct tokio_io::io::Read\">Read</a>&lt;R, T&gt; <span class=\"where fmt-newline\">where<br>&nbsp;&nbsp;&nbsp;&nbsp;R: <a class=\"trait\" href=\"tokio_io/trait.AsyncRead.html\" title=\"trait tokio_io::AsyncRead\">AsyncRead</a>,<br>&nbsp;&nbsp;&nbsp;&nbsp;T: <a class=\"trait\" href=\"https://doc.rust-lang.org/nightly/core/convert/trait.AsMut.html\" title=\"trait core::convert::AsMut\">AsMut</a>&lt;<a class=\"primitive\" href=\"https://doc.rust-lang.org/nightly/std/primitive.slice.html\">[</a><a class=\"primitive\" href=\"https://doc.rust-lang.org/nightly/std/primitive.u8.html\">u8</a><a class=\"primitive\" href=\"https://doc.rust-lang.org/nightly/std/primitive.slice.html\">]</a>&gt;,&nbsp;</span>","synthetic":false,"types":["tokio_io::io::read::Read"]},{"text":"impl&lt;A, T&gt; <a class=\"trait\" href=\"futures/future/trait.Future.html\" title=\"trait futures::future::Future\">Future</a> for <a class=\"struct\" href=\"tokio_io/io/struct.ReadExact.html\" title=\"struct tokio_io::io::ReadExact\">ReadExact</a>&lt;A, T&gt; <span class=\"where fmt-newline\">where<br>&nbsp;&nbsp;&nbsp;&nbsp;A: <a class=\"trait\" href=\"tokio_io/trait.AsyncRead.html\" title=\"trait tokio_io::AsyncRead\">AsyncRead</a>,<br>&nbsp;&nbsp;&nbsp;&nbsp;T: <a class=\"trait\" href=\"https://doc.rust-lang.org/nightly/core/convert/trait.AsMut.html\" title=\"trait core::convert::AsMut\">AsMut</a>&lt;<a class=\"primitive\" href=\"https://doc.rust-lang.org/nightly/std/primitive.slice.html\">[</a><a class=\"primitive\" href=\"https://doc.rust-lang.org/nightly/std/primitive.u8.html\">u8</a><a class=\"primitive\" href=\"https://doc.rust-lang.org/nightly/std/primitive.slice.html\">]</a>&gt;,&nbsp;</span>","synthetic":false,"types":["tokio_io::io::read_exact::ReadExact"]},{"text":"impl&lt;A&gt; <a class=\"trait\" href=\"futures/future/trait.Future.html\" title=\"trait futures::future::Future\">Future</a> for <a class=\"struct\" href=\"tokio_io/io/struct.ReadToEnd.html\" title=\"struct tokio_io::io::ReadToEnd\">ReadToEnd</a>&lt;A&gt; <span class=\"where fmt-newline\">where<br>&nbsp;&nbsp;&nbsp;&nbsp;A: <a class=\"trait\" href=\"tokio_io/trait.AsyncRead.html\" title=\"trait tokio_io::AsyncRead\">AsyncRead</a>,&nbsp;</span>","synthetic":false,"types":["tokio_io::io::read_to_end::ReadToEnd"]},{"text":"impl&lt;A&gt; <a class=\"trait\" href=\"futures/future/trait.Future.html\" title=\"trait futures::future::Future\">Future</a> for <a class=\"struct\" href=\"tokio_io/io/struct.ReadUntil.html\" title=\"struct tokio_io::io::ReadUntil\">ReadUntil</a>&lt;A&gt; <span class=\"where fmt-newline\">where<br>&nbsp;&nbsp;&nbsp;&nbsp;A: <a class=\"trait\" href=\"tokio_io/trait.AsyncRead.html\" title=\"trait tokio_io::AsyncRead\">AsyncRead</a> + <a class=\"trait\" href=\"https://doc.rust-lang.org/nightly/std/io/trait.BufRead.html\" title=\"trait std::io::BufRead\">BufRead</a>,&nbsp;</span>","synthetic":false,"types":["tokio_io::io::read_until::ReadUntil"]},{"text":"impl&lt;A&gt; <a class=\"trait\" href=\"futures/future/trait.Future.html\" title=\"trait futures::future::Future\">Future</a> for <a class=\"struct\" href=\"tokio_io/io/struct.Shutdown.html\" title=\"struct tokio_io::io::Shutdown\">Shutdown</a>&lt;A&gt; <span class=\"where fmt-newline\">where<br>&nbsp;&nbsp;&nbsp;&nbsp;A: <a class=\"trait\" href=\"tokio_io/trait.AsyncWrite.html\" title=\"trait tokio_io::AsyncWrite\">AsyncWrite</a>,&nbsp;</span>","synthetic":false,"types":["tokio_io::io::shutdown::Shutdown"]},{"text":"impl&lt;A, T&gt; <a class=\"trait\" href=\"futures/future/trait.Future.html\" title=\"trait futures::future::Future\">Future</a> for <a class=\"struct\" href=\"tokio_io/io/struct.WriteAll.html\" title=\"struct tokio_io::io::WriteAll\">WriteAll</a>&lt;A, T&gt; <span class=\"where fmt-newline\">where<br>&nbsp;&nbsp;&nbsp;&nbsp;A: <a class=\"trait\" href=\"tokio_io/trait.AsyncWrite.html\" title=\"trait tokio_io::AsyncWrite\">AsyncWrite</a>,<br>&nbsp;&nbsp;&nbsp;&nbsp;T: <a class=\"trait\" href=\"https://doc.rust-lang.org/nightly/core/convert/trait.AsRef.html\" title=\"trait core::convert::AsRef\">AsRef</a>&lt;<a class=\"primitive\" href=\"https://doc.rust-lang.org/nightly/std/primitive.slice.html\">[</a><a class=\"primitive\" href=\"https://doc.rust-lang.org/nightly/std/primitive.u8.html\">u8</a><a class=\"primitive\" href=\"https://doc.rust-lang.org/nightly/std/primitive.slice.html\">]</a>&gt;,&nbsp;</span>","synthetic":false,"types":["tokio_io::io::write_all::WriteAll"]}];
implementors["tokio_process"] = [{"text":"impl <a class=\"trait\" href=\"futures/future/trait.Future.html\" title=\"trait futures::future::Future\">Future</a> for <a class=\"struct\" href=\"tokio_process/struct.Child.html\" title=\"struct tokio_process::Child\">Child</a>","synthetic":false,"types":["tokio_process::Child"]},{"text":"impl <a class=\"trait\" href=\"futures/future/trait.Future.html\" title=\"trait futures::future::Future\">Future</a> for <a class=\"struct\" href=\"tokio_process/struct.WaitWithOutput.html\" title=\"struct tokio_process::WaitWithOutput\">WaitWithOutput</a>","synthetic":false,"types":["tokio_process::WaitWithOutput"]},{"text":"impl <a class=\"trait\" href=\"futures/future/trait.Future.html\" title=\"trait futures::future::Future\">Future</a> for <a class=\"struct\" href=\"tokio_process/struct.StatusAsync.html\" title=\"struct tokio_process::StatusAsync\">StatusAsync</a>","synthetic":false,"types":["tokio_process::StatusAsync"]},{"text":"impl <a class=\"trait\" href=\"futures/future/trait.Future.html\" title=\"trait futures::future::Future\">Future</a> for <a class=\"struct\" href=\"tokio_process/struct.OutputAsync.html\" title=\"struct tokio_process::OutputAsync\">OutputAsync</a>","synthetic":false,"types":["tokio_process::OutputAsync"]}];
implementors["tokio_reactor"] = [{"text":"impl <a class=\"trait\" href=\"futures/future/trait.Future.html\" title=\"trait futures::future::Future\">Future</a> for <a class=\"struct\" href=\"tokio_reactor/struct.Shutdown.html\" title=\"struct tokio_reactor::Shutdown\">Shutdown</a>","synthetic":false,"types":["tokio_reactor::background::Shutdown"]}];
implementors["tokio_sync"] = [{"text":"impl&lt;T&gt; <a class=\"trait\" href=\"futures/future/trait.Future.html\" title=\"trait futures::future::Future\">Future</a> for <a class=\"struct\" href=\"tokio_sync/oneshot/struct.Receiver.html\" title=\"struct tokio_sync::oneshot::Receiver\">Receiver</a>&lt;T&gt;","synthetic":false,"types":["tokio_sync::oneshot::Receiver"]}];
if (window.register_implementors) {window.register_implementors(implementors);} else {window.pending_implementors = implementors;}})()