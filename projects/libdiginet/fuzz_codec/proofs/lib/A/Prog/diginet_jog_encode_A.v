(* diginet_jog_encode (diginet_codec.c:156-165), image A 0x85190, 80 instructions, frame 16, no call: the walk
   against lib/A/Prog/CPgEncC.v's cdc_jog_specX. a0 = delta (an int, sign-extended), a1 = out (atom 11).
   0x85190 addi sp,sp,-16 and 0x85194 sd ra,8(sp) open the frame (the save area [sp - 16, sp)); 0x85198 beqz a1 is
   decided by out's fact (ceo_fact 11). The engine stops at one branch:
   0x851a4 bgeu a2,a3 with a2 = addiw a0,-64 and a3 = -128: BC_GEU (sext.w (delta - 64)) (2 ^ 64 - 128), which jog_br
   turns into -64 <= delta <= 63.
     not taken (delta out of range): 0x851a8 li a1,-11; j 0x85268; mv a0,a1; ld ra; addi sp; ret: a0 = -11 =
       E_RANGE = fst (jog_spec delta); nothing is written, so out is as it was (ceo_res_fail).
     TAKEN: out's three windows are added (ceo_add3). 0x851b8-0x851c0 load the shadow base through the .got slot
       0x9db10; the instrumented checks before the stores at out + 0, 1, 2, 24, 25 (1 byte) and out + 28 (4 bytes)
       are decided by the shadow entry mkSHE 11 0 32 (the error path is not reached); the stores put 176, 92,
       delta + 64 at out[0..3), 3 and 0 at out[24], out[25], and 0x80000 = KEY 8 0 at out[28..32); a0 = 0 at
       0x85274 ret (ceo_res_ok). *)
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
(* the spec first: DgnLib's st_ok (a running status) must not hide the engine's st_ok *)
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Spec Require Import DgnSpec DgnLib.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YN3v YI04 YI09 YI08 YI00.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq YC5d.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YI16 YM05.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require YImgTop.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.A Require Import AWalkFw0 ACef AF0l ACej ACeh ACem ACep.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.A Require Import AWalkFw1 AWalkFw2 ACfm.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.A.Prog Require Import CodecCJ CPgBase CPgEncC CPgWalk CPgEncOut.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.

(* ---- the branch at 0x851a4 and the result ---- *)
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
(* `addiw a2,a0,-64; li a3,-128; bgeu a2,a3` on the int delta: taken exactly when -64 <= delta <= 63 *)
Lemma jog_br : forall E delta, ew E 10 = Z_to_bv 64 delta -> - 2 ^ 31 <= delta < 2 ^ 31 ->
branch_taken BC_GEU (sv_denot E (SAluw ALU_ADD (SOff 10 0) (SLit (-64)))) (sv_denot E (SLit 18446744073709551488))
= (-64 <=? delta) && (delta <=? 63).
Proof.
intros E delta H Hd.
assert (H' : ew E 10 = Z_to_bv 64 (delta mod 2 ^ 64)).
{ rewrite H. apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64).
  rewrite Z.mod_mod by lia. reflexivity. }
rewrite branch_geu_U, (U_lit E 18446744073709551488) by lia.
rewrite U_of_S, S_SAluw. cbn [zalu_raw].
rewrite (U_atom E 10 (delta mod 2 ^ 64) H') by (apply Z.mod_pos_bound; lia).
rewrite U_SLit. change (zcanon (-64) mod 2 ^ 32) with 4294967232.
rewrite (Z.mod_mod_divide delta (2 ^ 64) (2 ^ 32)) by (exists (2 ^ 32); reflexivity).
unfold bv_swrap, bv_wrap. change (bv_half_modulus 32) with (2 ^ 31). change (bv_modulus 32) with (2 ^ 32).
change (bv_modulus 64) with (2 ^ 64).
match goal with |- negb (?x <? ?c) = _ => destruct (Z.ltb_spec x c) end;
destruct (Z.leb_spec (-64) delta); destruct (Z.leb_spec delta 63); cbn [negb andb]; first [reflexivity | exfalso; lia].
Qed.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Lemma jog_spec_ok : forall delta, -64 <= delta <= 63 ->
jog_spec delta = (0, Some ([0xb0; 0x5c; u8 (delta + 64)], KEY 8 0, 0)).
Proof.
intros delta H. unfold jog_spec. destruct (Z.ltb_spec delta (-64)); [lia|]. destruct (Z.ltb_spec 63 delta); [lia|].
reflexivity.
Qed.
Lemma jog_spec_fail : forall delta, delta < -64 \/ 63 < delta -> jog_spec delta = (E_RANGE, None).
Proof.
intros delta H. unfold jog_spec. destruct (Z.ltb_spec delta (-64)); [reflexivity|].
destruct (Z.ltb_spec 63 delta); [reflexivity | lia].
Qed.

Section b. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Variable B : asyms.
Variable MT : ameter_ops.
Hypothesis MTL : ameter_laws MT.
Hypothesis TL : TfibLib B.
Hypothesis LAWS : AR_laws tfibsegs B.
Theorem diginet_jog_encode_A_holds : cdc_jog_specX tfibsegs B MT 0x85190.
Proof using MTL TL LAWS.
unfold cdc_jog_specX.
intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs delta out before HE Hdelta H11 HO.
pose proof HE as HE0.
destruct HE as (HJ0 & Hra & Hra4 & Hgp & Htp & Hal16 & Hwlo & Hwhi & Hev & Hlive).
pose proof (proj1 HJ0) as HAR. pose proof HJ0 as HJ.
destruct Hdelta as (Hdr & H10).
pose proof HO as (HD & HG & HL).
pose proof HD as (Hq & Hqn & Htd & Htw & _ & _ & _ & Hcw).
unfold coff_win, T_jog in Hcw. unfold T_jog in Hwlo.
pose proof (ceo_off_img B STK sp0 FP ly S lyc Sc own W memc mdc (spZ regs) T_jog out HAR HD) as Himg.
unfold YImgTop.IMG_LO, YImgTop.IMG_TOP in Himg.
pose proof Hwx_tfa as Hwx. pose proof tfib_segs_low as Hsegs.
pose proof (ceo_entry B TL LAWS 0x85190 [] 11 (11%bv) [] STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs T_jog
  out HE0 ltac:(unfold T_jog; lia) eq_refl H11 HD I) as HS.
remember (Ereg regs (cw_extra [])) as E eqn:HEq.
assert (HAE : env_agree 32 (Ereg regs (cw_extra [])) E) by (subst E; apply env_agree_refl).
assert (E1 : ew E 1 = getr regs 1) by (subst E; exact (cw_ew_reg regs [] 1 1%bv eq_refl)).
assert (B2 : bv_unsigned (ew E 2) = spZ regs) by (subst E; rewrite (cw_ew_reg regs [] 2 2%bv eq_refl); reflexivity).
assert (E10 : ew E 10 = Z_to_bv 64 delta) by (subst E; rewrite (cw_ew_reg regs [] 10 10%bv eq_refl); exact H10).
assert (E11 : ew E 11 = Z_to_bv 64 out) by (subst E; rewrite (cw_ew_reg regs [] 11 11%bv eq_refl); exact H11).
assert (BO : bv_unsigned (ew E 11) = out) by (rewrite E11; apply unsigned_lit_small; lia).
assert (E32 : ew E 32 = Z_to_bv 64 SB) by (subst E; apply cw_ew_SB).
assert (SHOK : sh_ok tfibsegs CW_Bx [mkSHE 11 0 32] E (mrestrict (w_H W) memc)).
{ constructor; [|constructor].
  exact (cw_shent_cdst B STK sp0 FP ly S lyc Sc own W memc (spZ regs) T_jog E 11 out 32 HD E11 E32 ltac:(lia)). }
clear HEq.
assert (KE : forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - 16 <= a < spZ regs) ->
  aview tfibsegs (w_H W) memc a = aview tfibsegs (w_H W) memc a) by (intros; reflexivity).
unfold cfg_at. change (w64 0x85190) with (Z_to_bv 64 0x85190).
(* 0x85190-0x851a0; stop at 0x851a4 bgeu *)
cw_run cw_awr_stk. cw_keep cw_kwr_stk.
cw_branch Hb.
- (* bgeu TAKEN: -64 <= delta <= 63 *)
  rewrite (jog_br E delta E10 Hdr) in Hb. apply andb_true_iff in Hb as [Hb1 Hb2]. apply Z.leb_le in Hb1, Hb2.
  (* out's three windows, then KE over ceo_zone *)
  lazymatch goal with HS0 : st_ok _ _ ?ss (restrict (w_H W) ?ms) |- _ =>
    pose proof (ceo_add3 B LAWS STK sp0 FP ly S lyc Sc own W memc mdc (spZ regs) T_jog E ss ms 11 out 3 HAR HD HS0 BO
      ltac:(lia) ltac:(intros a Ha; apply KE; lia)
      ltac:(ceo_disj ltac:(clear - Hcw Himg; lia)) ltac:(ceo_disj ltac:(clear - Hcw Himg; lia))
      ltac:(ceo_disj ltac:(clear - Hcw Himg; lia))) as HS1;
    clear HS0; rename HS1 into HS end.
  pose proof (ceo_KE_widen _ _ _ (spZ regs) out 3 KE) as KE1. clear KE. rename KE1 into KE.
  (* 0x851b8-0x85274: the shadow base, the six checks, the stores; stop at ret *)
  cw_run ltac:(ceo_awr Htw).
  cw_keep ceo_kwr.
  cw_leaf ltac:(idtac; cw_kept HJ0 KE
      ltac:(intros a Ha Him; exact (ceo_eimg B LAWS STK sp0 FP ly S lyc Sc own W memc mdc (spZ regs) T_jog out a HAR HD Ha Him))
      ltac:(intros a Ha; cbv beta in Ha; unfold cenc_wr, T_jog; try unfold ceo_zone in Ha; lia))
    idtac.
  rewrite (jog_spec_ok delta ltac:(lia)). unfold cenc_res. cbn [fst snd].
  split; [ceo_a0 R10|].
  lazymatch goal with HS0 : st_ok _ _ _ _ |- _ => ceo_chunks HS0 end.
  eapply (ceo_res_ok _ memc _ out before [0xb0; 0x5c; u8 (delta + 64)] (KEY 8 0) 0 HL ltac:(cbn; lia) HG).
  + intros j Hj. cbn [length] in Hj.
    destruct j as [|[|[|j]]]; [| | | lia]; cbn [nth Z.of_nat]; (eapply ceo_chunk1; [eassumption|]).
    * rewrite U_lit by lia. reflexivity.
    * rewrite U_lit by lia. reflexivity.
    * erewrite ceo_U_off by exact E10. unfold u8. rewrite Z.mod_mod by lia. reflexivity.
  + eapply ceo_chunk1; [eassumption|]. rewrite U_lit by lia. reflexivity.
  + eapply ceo_chunk1; [eassumption|]. rewrite U_lit by lia. reflexivity.
  + intros j Hj. eapply ceo_chunk4; [eassumption | rewrite U_lit by lia; vm_compute; reflexivity | exact Hj].
  + intros a Ha. change (Z.of_nat (length [0xb0; 0x5c; u8 (delta + 64)])) with 3 in Ha.
    apply KE; [lia | unfold ceo_zone; lia].
- (* bgeu not taken: delta < -64 or 63 < delta; to 0x851a8, a0 = -11 at ret *)
  rewrite (jog_br E delta E10 Hdr) in Hb.
  assert (Hout : delta < -64 \/ 63 < delta)
    by (apply andb_false_iff in Hb; destruct Hb as [Hb|Hb]; apply Z.leb_gt in Hb; lia).
  cw_run cw_awr_stk. cw_keep cw_kwr_stk.
  cw_leaf ltac:(idtac; cw_kept HJ0 KE
      ltac:(intros a Ha Him; exact (ceo_eimg B LAWS STK sp0 FP ly S lyc Sc own W memc mdc (spZ regs) T_jog out a HAR HD Ha Him))
      ltac:(intros a Ha; cbv beta in Ha; unfold cenc_wr, T_jog; lia))
    idtac.
  rewrite (jog_spec_fail delta Hout).
  apply (ceo_res_fail W memc _ _ out before (spZ regs) E_RANGE HG HL ltac:(lia) ltac:(lia) Hcw KE).
  ceo_a0 R10.
Qed.
End b.
