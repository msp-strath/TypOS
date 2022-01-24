;; based on: http://ergoemacs.org/emacs/elisp_syntax_coloring.html

;; define several class of keywords
(setq typos-keywords  '("syntax" "exec" "case" "BREAK"))
(setq typos-operators '("@" "!" "?" "~" "#" "|"))
(setq typos-symbols   '("->" ";" "=" "{" "}"))

;; create the regex string for each class of keywords
(setq typos-keywords-regexp  (regexp-opt typos-keywords 'words))
(setq typos-operators-regexp (regexp-opt typos-operators))
(setq typos-symbols-regexp   (regexp-opt typos-symbols))

;; clear memory
(setq typos-keywords  nil)
(setq typos-operators nil)
(setq typos-symbols   nil)

;; create the list for font-lock.
;; each class of keyword is given a particular face
(setq typos-font-lock-keywords
  `(
    (,typos-operators-regexp . font-lock-builtin-face)
    (,typos-keywords-regexp  . font-lock-keyword-face)
    (,typos-symbols-regexp   . font-lock-builtin-face)
))

;; syntax table
(defvar typos-syntax-table nil "Syntax table for `typos-mode'.")
(setq typos-syntax-table
  (let ((synTable (make-syntax-table)))

  ;; comments
  (modify-syntax-entry ?\{  "(}1nb" synTable)
  (modify-syntax-entry ?\}  "){4nb" synTable)
  (modify-syntax-entry ?-  "_ 123" synTable)
  (modify-syntax-entry ?\n ">" synTable)

        synTable))

;; define the mode
(define-derived-mode typos-mode fundamental-mode
  "TYPOS mode"
  ;; handling comments
  :syntax-table typos-syntax-table
  ;; code for syntax highlighting
  (setq font-lock-defaults '((typos-font-lock-keywords)))
  (setq mode-name "typos")
  ;; clear memory
  (setq typos-keywords-regexp nil)
  (setq typos-operators-regexp nil)
)

(provide 'typos-mode)
