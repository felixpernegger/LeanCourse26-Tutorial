// When served locally (`./slides serve`), reload the page once `./slides build` has finished writing a
// new version (it writes `build-stamp.txt` last). reveal.js keeps the current slide in the URL, so the reload stays on the same slide.
(function () {
    "use strict";
    if (!["localhost", "127.0.0.1"].includes(location.hostname)) return;
    var last = null;
    setInterval(function () {
        fetch("build-stamp.txt", { cache: "no-store" })
            .then(function (r) { return r.ok ? r.text() : null; })
            .then(function (stamp) {
                if (stamp === null) return;
                if (last !== null && stamp !== last) location.reload();
                last = stamp;
            })
            .catch(function () {});
    }, 1000);
})();
