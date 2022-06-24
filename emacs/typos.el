(require 'compile)

;; based on: http://ergoemacs.org/emacs/elisp_syntax_coloring.html

;; define several class of keywords
(setq typos-keywords  '("syntax" "exec" "trace"
                        "break" "unify" "send" "recv" "move"
                        "case" "if" "let" "in" "else"
                        "Atom" "AtomBar" "Wildcard" "EnumOrTag" "Enum" "Tag" "Cons" "Nil" "NilOrCons" "Fix" "Bind"
                        "BREAK" "PRINT" "PRINTF"))
(setq typos-operators '("@" "!" "?" "~" "#"))
(setq typos-symbols   '("|-" "|" "<->" "->" ";" "=" "{" "}"))

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
  "TypOS mode"
  ;; handling comments
  :syntax-table typos-syntax-table
  ;; code for syntax highlighting
  (setq font-lock-defaults '((typos-font-lock-keywords)))
  (setq mode-name "typos")
  ;; clear memory
  (setq typos-keywords-regexp nil)
  (setq typos-operators-regexp nil)
)

;; Customisation options

(defgroup typos nil
  "An operating system for typechecking processes."
  :group 'languages)

(defcustom typos-command "typos"
  "The path to the typOS command to run."
  :type 'string
  :group 'typos)

(defcustom typos-options nil
  "Command line options to pass to typOS."
  :type 'string
  :group 'typos)

;; Compilation mode for running typOS
;; (based on https://spin.atomicobject.com/2016/05/27/write-emacs-package/ )

(defun typos-compilation-filter ()
  "Filter function for compilation output."
  (ansi-color-apply-on-region compilation-filter-start (point-max)))

(define-compilation-mode typos-compilation-mode "TypOS"
  "TypOS compilation mode."
  (progn
    (set (make-local-variable 'compilation-error-regexp-alist)
         '(("\\(^[^[:space:]]*\\):\\([0-9]+\\):\\([0-9]+\\)-\\(\\([0-9]+\\):\\)?\\([0-9]+\\)$"
            1 (2 . 5) (3 . 6))
           ("^Parse error \\(at\\|near\\) location: \\([^[:space:]]*\\):\\([0-9]+\\):\\([0-9]+\\)"
            2 3 (4 . 5))))
    (add-hook 'compilation-filter-hook 'typos-compilation-filter nil t)))

(defface typos-highlight-error-face
  '((t (:underline (:color "red" :style wave))))
  "The face used for errors.")

(defun typos-run-on-file (typos-file options)
  "Run typOS in a compilation buffer on TYPOS-FILE."
  (setq compilation-auto-jump-to-first-error t)
  (setq next-error-highlight-timer t)
  (setq next-error-highlight t)
  (setq typos-error-highlight (make-overlay (point-min) (point-min)))
  (overlay-put typos-error-highlight 'face 'typos-highlight-error-face)
  (setq compilation-highlight-overlay typos-error-highlight)
  (save-some-buffers compilation-ask-about-save
                     (when (boundp 'compilation-save-buffers-predicate)
                       compilation-save-buffers-predicate))

  (when (get-buffer "*typos output*")
    (kill-buffer "*typos output*"))
  (let ((typos-command-to-run (concat typos-command " " options " " typos-file)))
    (with-current-buffer (get-buffer-create "*typos output*")
      (compilation-start typos-command-to-run 'typos-compilation-mode (lambda (m) (buffer-name)))
      (overlay-put (make-overlay (point-min) (point-max) (current-buffer) nil t)
                   'face
                   `(:background "black",:foreground "white",:extend t)))))

;;;###autoload
(defun typos-run (override-options)
  "Run typOS on the current file."
  (interactive "P")
  (let ((opts (if override-options (read-string "Options: ") typos-options)))
    (typos-run-on-file (shell-quote-argument (buffer-file-name)) opts)))

(define-key typos-mode-map (kbd "C-c C-l") 'typos-run)

(provide 'typos-mode)
