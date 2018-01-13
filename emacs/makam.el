;; makam.el - Proof General for Makam.

(require 'proof-easy-config)
(require 'proof-syntax)

(proof-easy-config 'makam "Makam"

 proof-prog-name		     "makam"
 proof-script-command-end-regexp     "\\.[ \n\r\t]\\|\\?[ \n\r\t]"        ;; end of commands
 proof-script-comment-start          "(*"	;; comments
 proof-script-comment-end            "*)"	;; comments
 proof-shell-annotated-prompt-regexp "## Ready for input." ;; matches prompts

 proof-shell-strip-crs-from-input nil
 proof-script-fly-past-comments  t

 proof-shell-error-regexp            "^.. Error in.*:"
 proof-shell-interrupt-regexp        "^.*Interrupted."
 proof-shell-result-start            ""
 proof-shell-result-end              "## Ready for input."
 proof-shell-restart                 "%%reset.\n"
 proof-forget-id-command             "%%forget %s.\n"
 proof-shell-handle-output-system-specific
    '(lambda (cmd string) (proof-shell-display-output-as-response
			     proof-shell-delayed-output-flags
			     string))
    
 ;; next setting is just to prevent warning
 proof-save-command-regexp	proof-no-regexp
 )

(provide 'makam)

