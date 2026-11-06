(* The program functions the listing calls by name (IS_<f>, a call slot of ident_listing) and where each one starts:
   BASE + AF_<f> (BASE = pa_val A_TEXT, the listing's first slot). A walk that calls a program function f takes the
   callee's contract at BASE + AF_<f>, while the engine is at pa_sigma IS_<f> after the call; prog_sig_ok relates the
   two for every program function at once. It is one Section hypothesis per walk file, proved once for fuzz_identity.asan
   (IdentProgSigImg.v). *)
From Stdlib Require Import ZArith.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YK11 YM05.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.A.Prog Require Import PaTable PaSym.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.A.Prog Require Import IdentSyms IdentList IdentPa.
Open Scope Z_scope.
Definition ident_prog_af (s : isym) : option Z :=
match s with
| IS_check_str => Some AF_check_str
| IS_put_dec => Some AF_put_dec
| IS_reac_box_family_of => Some AF_reac_box_family_of
| IS_reac_box_family_stem => Some AF_reac_box_family_stem
| IS_reac_box_name => Some AF_reac_box_name
| IS_sb_dec => Some AF_sb_dec
| IS_reac_box_catalogue_defect => Some AF_reac_box_catalogue_defect
| IS_reac_box_catalogue => Some AF_reac_box_catalogue
| IS_reac_identity_init => Some AF_reac_identity_init
| IS_reac_identity_ingest => Some AF_reac_identity_ingest
| IS_reac_identity_fw_str => Some AF_reac_identity_fw_str
| IS_reac_identity_reac_ver_str => Some AF_reac_identity_reac_ver_str
| IS_write_uint => Some AF_write_uint
| _ => None
end.
Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {PI : PAImg ident_listing}.
Definition ident_prog_sig_ok : Prop :=
  forall s af, ident_prog_af s = Some af -> @pa_sigma _ ident_listing PI s = @pa_val _ ident_listing PI A_TEXT + af.
End a.
