(* The program functions the listing calls by name (IB_<f>, a call slot of identb_listing) and where each one starts:
   BASE + AF_<f> (BASE = pa_val A_TEXT, the listing's first slot). A walk that calls a program function f takes the
   callee's contract at BASE + AF_<f>, while the engine is at pa_sigma IB_<f> after the call; prog_sig_ok relates the
   two for every program function at once. It is one Section hypothesis per walk file, proved once for fuzz_identity.asan-ubsan
   (IdentBProgSigImg.v). *)
From Stdlib Require Import ZArith.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YK11 YM05.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.A.Prog Require Import PaTable PaSym.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.B.Prog Require Import IdentBSyms IdentBList IdentBPa.
Open Scope Z_scope.
Definition identb_prog_af (s : ibsym) : option Z :=
match s with
| IB_check_str => Some AF_check_str
| IB_put_dec => Some AF_put_dec
| IB_reac_box_family_of => Some AF_reac_box_family_of
| IB_reac_box_family_stem => Some AF_reac_box_family_stem
| IB_reac_box_name => Some AF_reac_box_name
| IB_sb_dec => Some AF_sb_dec
| IB_reac_box_catalogue_defect => Some AF_reac_box_catalogue_defect
| IB_reac_box_catalogue => Some AF_reac_box_catalogue
| IB_reac_identity_init => Some AF_reac_identity_init
| IB_reac_identity_ingest => Some AF_reac_identity_ingest
| IB_reac_identity_fw_str => Some AF_reac_identity_fw_str
| IB_reac_identity_reac_ver_str => Some AF_reac_identity_reac_ver_str
| IB_write_uint => Some AF_write_uint
| IB_buf_of => Some AF_buf_of
| IB_sb_ch => Some AF_sb_ch
| _ => None
end.
Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {PI : PAImg identb_listing}.
Definition identb_prog_sig_ok : Prop :=
  forall s af, identb_prog_af s = Some af -> @pa_sigma _ identb_listing PI s = @pa_val _ identb_listing PI A_TEXT + af.
End a.
