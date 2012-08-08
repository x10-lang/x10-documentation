(defun bard-pg-fix-xlrefs-in-tex-file ()
  (interactive)
  (save-excursion
    (goto-char (point-min))
    (while
        (search-forward "\\xlref{" (point-max) t)
      (when (search-forward "}{" (+ (point) 100) t)
        (replace-match "-")))))

(defun bard-pg-insert-xlref-in-x10 (lid)
  (interactive "sLine name: ")
  (let ((fid (bard-pg-find-fid-in-x10)))
    (insert-format
     "// \\xlref{%s-%s}" fid lid)))

(defun bard-pg-find-fid-in-x10 ()
  (save-excursion
    (search-backward-regexp "//START TeX: *\\([a-zA-Z0-9---]+\\)")
    (match-string 1)))



(define-key x10-mode-map [?\C-c ?\C-l] 'bard-pg-insert-xlref-in-x10)
(define-key x10-mode-map [?\C-c ?\C-s] "//START TeX:")
(define-key x10-mode-map [?\C-c ?\C-e] "//END TeX:")
(define-key x10-mode-map [?\C-c ?\C-p] "//PAUSE TeX:")
(define-key x10-mode-map [?\C-c ?\C-r] "//RESUME TeX:")
      
