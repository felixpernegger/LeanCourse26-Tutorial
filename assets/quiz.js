// Click a hidden answer box inside a `quiz` block to reveal it (click again to hide). See custom.css.
document.addEventListener("click", function (e) {
    var box = e.target.closest && e.target.closest(".quiz .command-output");
    if (box) box.classList.toggle("revealed");
});
