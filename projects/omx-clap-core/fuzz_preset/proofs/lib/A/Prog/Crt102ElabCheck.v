(* fuzz_preset, the crt102 walk: THE ELABORATION CHECK of its statements (the family lead's rule, 2026-10-29:
   a class-implicit FPState can resolve to the wrong one and the statement still type-checks and proves).

   YK11.FPState is a Class (YK11.v:15). So any glue predicate that depends on the Section's `fx` takes it as an
   implicit instance argument, and an application that omits `(fx := ..)` while a second FPState (`fxk`) is bound is
   resolved by instance search, which can pick `fxk`. This file prints, with implicit arguments shown:
   (1) the argument list of every glue predicate, so the reader sees WHICH depend on an FPState at all;
   (2) the elaborated statement of each landed slice's top lemma, so the reader sees what `fx` resolved to.
   It proves nothing and is read from the build log. Built through pins102 like every lane file.

   Inputs of record: as Crt102Glue.v's header (contract texts fab331f29a65, PresetReqAt 379c33e9e482,
   engine 459129c18903, listing v3 74dcda1eda12, route pins102). *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A.Prog Require Crt102Glue Crt102Entry Crt102Arms Crt102Kit.

Set Printing Implicit.

(* (1) which glue predicates take an FPState *)
About Crt102Glue.QT.
About Crt102Glue.QF.
About Crt102Glue.crt_side.
About Crt102Glue.crt_live.
About Crt102Glue.crt_pos.
About Crt102Glue.crt_cfg.
About Crt102Glue.crt_bregs.
About Crt102Glue.crt_dregs.
About Crt102Glue.crt_copy_zero.
About Crt102Glue.crt_at_J.
About Crt102Glue.crt_at_J_B.
About Crt102Glue.crt_at_X.
About Crt102Glue.crt_at_X_B.
About Crt102Glue.crt_at_U.
About Crt102Glue.crt_at_U_B.
About Crt102Glue.crt_at_W_B.
About Crt102Glue.crt_at_L0.
About Crt102Glue.crt_at_L0_B.
About Crt102Glue.crt_at_L3_B.
About Crt102Glue.crt_at_C_B.

(* (2) the landed slices' top lemmas, elaborated *)
Check @Crt102Entry.crt102_entry.
Check @Crt102Arms.arms_at_M.
Check @Crt102Kit.crt102rw_at_X.

(* (3) the family lead's amendment (2026-10-29): About / Check print a TYPE, and a second FPState inside a Prop BODY stays
   hidden. So every DEFINITION whose body is a Prop is PRINTED with implicits on and notations off, and its body read:
   the class position must hold the binder `fx` everywhere, and the current state `fxk` may appear only as an explicit
   argument (fregs_kept_x fx fxk, frm_zero (fp_csr fxk), crt_cfg fxk ..). Theorems keep `Check @` above. *)
Unset Printing Notations.
Print Crt102Glue.QT.
Print Crt102Glue.QF.
Print Crt102Glue.crt_side.
Print Crt102Glue.crt_live.
Print Crt102Glue.crt_pos.
Print Crt102Glue.crt_at_J.
Print Crt102Glue.crt_at_J_B.
Print Crt102Glue.crt_at_X.
Print Crt102Glue.crt_at_X_B.
Print Crt102Glue.crt_at_U.
Print Crt102Glue.crt_at_U_B.
Print Crt102Glue.crt_at_W_B.
Print Crt102Glue.crt_at_L0.
Print Crt102Glue.crt_at_L0_B.
Print Crt102Glue.crt_at_L3_B.
Print Crt102Glue.crt_at_C_B.
Print Crt102Glue.CRT_B_AT_X.
Print Crt102Glue.CRT_B_AT_C.
Print Crt102Glue.CRT_B_AT_L3.
Print Crt102Glue.CRT_B_AT_L0.

(* (4) the family lead's lexing check: a lemma swallowed by a stray double-quote or comment-closer inside a comment builds
   green and still shows in git grep. Locate against the compiled .vo must print Constant and a path for every exported
   lemma; a missing one prints No object of basename. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A.Prog Require Crt102Img Crt102Model Crt102Tail Crt102AF0lCheck.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B.Prog Require CrtImgB102.
Locate Crt102Entry.crt102_entry.
Locate Crt102Arms.arms_at_M.
Locate Crt102Kit.crt102rw_at_X.
Locate Crt102Img.crt102_cap.
Locate Crt102Img.crt102_smx.
Locate Crt102Model.cm_cap_of_tblk.
Locate Crt102Tail.ct_r0_end.
Locate Crt102Tail.ct_J_call.
Locate Crt102Tail.ct_at_Z.
Locate Crt102AF0lCheck.crt102_af0l_stack_malloc3.

(* (5) the composition and the A' binding (Crt102Top, Crt102PALibCheck): theorems, so their TYPE is the statement *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A.Prog Require Crt102Top Crt102PALibCheck.
Set Printing Notations.
Check @Crt102Top.crt102_top_of.
Check @Crt102Top.crt102_top_of_TfibA.
Check @Crt102Top.crt102_top_X_J.
Check @Crt102PALibCheck.crt102_palibcore_A.
Locate Crt102Top.crt102_top_of.
Locate Crt102Top.crt102_top_of_TfibA.
Locate Crt102Top.crt102_top_X_J.
Locate Crt102PALibCheck.crt102_palibcore_A.
Print Assumptions Crt102Top.crt102_top_of.
Print Assumptions Crt102Top.crt102_top_of_TfibA.
