; Working from the tutorial at http://two-wugs.net/emacs/mode-tutorial.html

(eval-when-compile
  (require 'cl))

; alternative idea: do not include the regexp in format-alist, but
; have a new major mode that works automatically applies the correct
; format

;should probably do the following using "magic" file names (see info)
;; (add-to-list 'format-alist
;; 	     '(java-class-file
;; 	       "Java class file"
;; 	       "\\`\312\376\272\276"
;; 	       "/home/bob/working/request-repo/progs/ocaml-jvml-bob/jdis"
;; 	       "/home/bob/working/request-repo/progs/ocaml-jvml-bob/jas"
;; 	       t
;; 	       nil))

;; (add-to-list 'file-coding-system-alist
;; 	     '("\\.class\\'" no-conversion . no-conversion))

;; (add-to-list 'auto-mode-alist '("\\.class$" . jvmasm-mode))

(add-to-list 'auto-mode-alist '("\\.j$" . jvmasm-mode))

(define-derived-mode jvmasm-mode fundamental-mode "JVMASM"
  "Major mode for editing JVM assembler files"
  (set (make-local-variable 'comment-start) "; ")
  (set (make-local-variable 'comment-start-skip) ";+\\s-*")
  (set (make-local-variable 'font-lock-defaults) '(jvmasm-font-lock-keywords))
  (set (make-local-variable 'indent-line-function) 'jvmasm-indent-line)
  (setq imenu-generic-expression jvmasm-imenu-generic-expression)
  (imenu-add-to-menubar "Jvmasm-Declarations"))

(defvar jvmasm-font-lock-keywords
  (list
   '("\\(^\\|[[:blank:]]\\);.*$" . font-lock-comment-face)
   '("\\(^\\|[[:blank:]]\\)\\.[^[:space:]]+" . font-lock-keyword-face)
   '("[A-Za-z0-9]+:" . font-lock-function-name-face))
  "Font lock keywords")

(setq jvmasm-imenu-generic-expression
      '((nil "^.method.*[[:blank:]]+\\([^[:space:]]+\\)[[:blank:]]+(" 1)
	(nil  "^.field.*[[:blank:]]+\\([^[:space:]]+\\)[[:blank:]]+[^[:space:]]+[[:blank:]]*$" 1)))

(defvar jvmasm-default-indent
  2
  "Default amount to indent for JVM assembler mode")

(defconst jvmasm-indent
  "^[ \t]*\\.\\(method\\|field\\|code\\|annotation\\|element[[:blank:]]+[^[:blank:]]+[[:blank:]]+\\.\\(annotation\\|array\\)\\)")

(defconst jvmasm-label
  "^[ \t]*[A-Za-z0-9]+:")

(defconst jvmasm-undent
  "^[ \t]*\\.end")

(defun jvmasm-indent-amount ()
  "Compute the indentation for the line at point"
  (beginning-of-line)
  (save-excursion
    (max
     0
     (+ (if (looking-at jvmasm-label) -1 0)
	(cond
	 ((bobp)
	  0)
	 ((looking-at jvmasm-undent)
	  (forward-line -1)
	  (cond ((looking-at jvmasm-indent) (current-indentation))
		((looking-at jvmasm-label)  (- (current-indentation) jvmasm-default-indent -1))
		(t                          (- (current-indentation) jvmasm-default-indent))))
	 (t
	  (loop
	   (forward-line -1)
	   (cond ((looking-at jvmasm-undent) (return (current-indentation)))
		 ((looking-at jvmasm-indent) (return (+ (current-indentation) jvmasm-default-indent)))
		 ((bobp)                     (return 0))))))))))

(defun jvmasm-indent-line ()
  "Indent current line in JVM assembler mode"
  (interactive)
  (indent-line-to (jvmasm-indent-amount)))

(provide 'jvmasm-mode)
