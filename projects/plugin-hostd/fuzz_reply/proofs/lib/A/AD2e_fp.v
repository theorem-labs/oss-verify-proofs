(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: new file holding text copied from A/AD2e.v (lines 63-134, 321-382) with renamed
   definitions: the PAYLOAD path's entry into target_run's loop (malloc + memcpy of the payload, then the first call at
   S_PL0 / S_PL1) onto A/AD2f_fp.v's clipped call-site view: refines_PM_LF and pl_to_LF are the donor's refines_PM_L and
   pl_to_L with L_mem / S_L replaced by L_memF / S_LF, the image regions of IMG_E cut by clipLF (fuzz_reply's program
   globals G_fr_c out).  PL_gf_start is the twin of A/AD2d_fp.v sPE_gf_start at S_PL0 / S_PL1: every byte of the 20
   program objects reads its image byte and is writable there.  rom_view at S_PL is A/AD1r_fp.v rom_view_of_arodata
   applied to A/AD2e.v PL_img_facts. *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Sem.
From OSSVerify.plugin_hostd.fuzz_reply.images Require Import Asan.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YO0d YO0f.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YK11 YK00 YK0h YK14 YK1b YK15 YK18 YK0p YP0n YK0s YM02 YP0m YP09 YP02 YP0l YP0k YP06 YP08 YP03 YP0g YP0e YN3q YN3v YI04 YL0a YL09 YL02 YL04 YK04 YA0i YA0n YA0o YA0p YA0m YK09 YA0e YG00 YG01 YG0k YG0f YG0v YG0n YG0d YCe5.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import AB1v AB12 AF0l AB1h AB13 AF0m AD2j AD2i AD1t AD20.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YD2n.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import AD1v AD1y AD26 AD24.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import AD21 AD25 AD23 AD2h AD1w AD2f AD2b AD2g AD1s AD2c AD2d AD29 AD2e.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YO05 YO09 YO06 YO01.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import AE2k AD1u.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import AD2f_fp AD2d_fp.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Open Scope Z_scope.

(* ---- the clipped pieces (AD2e.v:63-76) ---- *)
Definition PM_tailLF : list smem := map (fun r => [r]) (firstn 2 (skipn 1 (ss_mem S_Pm))) ++ map clipLF IMG_E.
Definition PM_piecesLF : list smem := [WIN208] :: [TRF] :: PM_tailLF.
Lemma PM_piecesLF_eq : concat PM_piecesLF = L_memF /\ length PM_piecesLF = length (WIN (-208) :: rsPL).
Proof. vm_compute. split; reflexivity. Qed.
Section b. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {LS : lib_shape}.
#[local] Ltac sub_piece Hr :=
eapply region_ok_sub; [| cbn; lia | exact Hr]; split; [reflexivity|]; split; [cbn; lia|]; split; [cbn; lia|];
split; [cbn; first [left; lia | right; lia] | intros c Hc; cbn in Hc |- *; tauto].
Lemma refines_PM_tailLF : forall E3 (m : word -> option byte), refines E3 m (firstn 2 (skipn 1 (ss_mem S_Pm)) ++ IMG_E) PM_tailLF.
Proof.
intros E3 m. unfold PM_tailLF. apply refines_app; [apply refines_single|].
apply refines_map. intros r Hr. pose proof (proj1 (forallb_forall _ _) IMG_E_lohi r Hr) as Hlh. cbn beta in Hlh. apply Z.leb_le in Hlh.
apply clipLF_ok. exact Hlh.
Qed.
Lemma refines_PM_LF : forall E3 (m : word -> option byte), refines E3 m (WIN (-208) :: rsPL) PM_piecesLF.
Proof.
intros E3 m. rewrite rsPL_split. unfold PM_piecesLF.
apply refines_cons; [intros Hr; constructor; [exact Hr | constructor] | constructor; [apply ext_in_refl | constructor] | cbn; split; exact I |].
apply refines_cons; [intros Hr; constructor; [sub_piece Hr | constructor] | constructor; [unfold ext_in; cbn; repeat split; first [reflexivity | lia] | constructor] | cbn; split; exact I |].
apply refines_PM_tailLF.
Qed.

(* ---- the payload path's first call onto the clipped view (AD2e.v:321-382) ---- *)
Lemma pl_to_LF : forall (c0 : bool) (k : Z) E4 (W : world tfibsegs) ms (n q : Z),
st_ok tfibsegs E4 (if c0 then S_PL0 else S_PL1 k) (restrict (w_H W) ms) ->
U E4 sv_pl00 = n -> 0 <= n <= 2 ^ 26 -> bv_unsigned (ew E4 A_PBLK) = q -> 4096 <= q -> q <= 2 ^ 47 -> 1 <= k <= 4 -> (c0 = true -> k = 1) ->
let E' := E_L E4 (ms_regs ms) in
st_ok tfibsegs E' S_LF (restrict (w_H W) ms)
/\ bv_unsigned (ew E' 162) = n /\ bv_unsigned (ew E' 163) = q /\ bv_unsigned (ew E' 164) = q /\ bv_unsigned (ew E' 166) = k
/\ (forall j, (j < K_L)%nat -> ew E' j = ew E4 j).
Proof.
intros c0 k E4 W ms n q HS Hn Hnb Hq Hq1 Hq2 Hk Hc0 E'.
set (ss := if c0 then S_PL0 else S_PL1 k) in *. set (regs := ms_regs ms) in *.
pose proof (PL_if c0 k) as (MPL & PCL & RVL & _ & CHK & _). fold ss in MPL, PCL, RVL, CHK.
pose proof S_PL_regs as (P8a & P8b & P9a & P9b & P10a & P10b & P11a & P11b & P18a & P18b & P20a & P20b & _).
assert (R : forall r v, (sr_get (ss_regs S_PL0) r = v /\ sr_get (ss_regs (S_PL1 k)) r = v) -> getr regs r = sv_denot E4 v).
{ intros r v [H0 H1]. subst regs. rewrite (st_ok_restrict_reg tfibsegs (w_H W) E4 ss ms r HS). subst ss. destruct c0; [rewrite H0 | rewrite H1]; reflexivity. }
assert (R8 : getr regs 8%bv = sv_denot E4 sv_pl00) by (apply R; split; [exact P8a | exact (P8b k)]).
assert (R9 : getr regs 9%bv = sv_denot E4 (SOff A_PBLK 0)) by (apply R; split; [exact P9a | exact (P9b k)]).
assert (R10 : getr regs 10%bv = sv_denot E4 (SOff A_PBLK 0)) by (apply R; split; [exact P10a | exact (P10b k)]).
assert (R11 : getr regs 11%bv = sv_denot E4 (add0 sv_pl00)) by (apply R; split; [exact P11a | exact (P11b k)]).
assert (R18 : getr regs 18%bv = sv_denot E4 (SOff A_PBLK 0)) by (apply R; split; [exact P18a | exact (P18b k)]).
assert (R20 : getr regs 21%bv = w64 k).
{ subst regs. rewrite (st_ok_restrict_reg tfibsegs (w_H W) E4 ss ms 21%bv HS). subst ss. destruct c0; [rewrite (Hc0 eq_refl), P20a | rewrite (P20b k)]; reflexivity. }
assert (R8_11 : getr regs 11%bv = getr regs 8%bv) by (rewrite R8, R11, !denot_lit_U, U_add0; reflexivity).
assert (NEW : forall i r, (i < 18)%nat -> nth i L_srcs 0%bv = r -> ew E' (K_L + i) = getr regs r).
{ intros i r Hi <-. subst E'. unfold E_L. rewrite (ew_havoc_new E4 K_L _ i (getr regs 0%bv)) by (rewrite length_map; exact Hi). apply map_nth. }
assert (Eold : forall j, (j < K_L)%nat -> ew E' j = ew E4 j) by (intros j Hj; subst E'; unfold E_L; apply ew_havoc_old; exact Hj).
assert (Q83 : sv_denot E4 (SOff A_PBLK 0) = w64 q) by (cbn [sv_denot]; rewrite Z.add_0_r, <- Hq; reflexivity).
assert (V61 : bv_unsigned (ew E' 162) = n).
{ change 162%nat with (K_L + 0)%nat. rewrite (NEW 0%nat 8%bv) by (cbn; first [lia | reflexivity]). rewrite R8. rewrite denot_lit_U, Hn. apply u64_lit. lia. }
assert (V62 : bv_unsigned (ew E' 163) = q).
{ change 163%nat with (K_L + 1)%nat. rewrite (NEW 1%nat 9%bv) by (cbn; first [lia | reflexivity]). rewrite R9, Q83. apply u64_lit. lia. }
assert (V63 : bv_unsigned (ew E' 164) = q).
{ change 164%nat with (K_L + 2)%nat. rewrite (NEW 2%nat 18%bv) by (cbn; first [lia | reflexivity]). rewrite R18, Q83. apply u64_lit. lia. }
assert (V65 : bv_unsigned (ew E' 166) = k).
{ change 166%nat with (K_L + 4)%nat. rewrite (NEW 4%nat 21%bv) by (cbn; first [lia | reflexivity]). rewrite R20. apply u64_lit. lia. }
split; [| repeat split; assumption].
pose proof (st_ok_mem_ok tfibsegs E4 ss _ HS) as HM0. cbn [restrict ms_mem] in HM0. rewrite MPL in HM0.
assert (HM1 : mem_ok tfibsegs E4 (mrestrict (w_H W) (ms_mem ms)) L_memF).
{ rewrite <- (proj1 PM_piecesLF_eq). apply (mem_ok_refine E4 _ (WIN (-208) :: rsPL)); [exact HM0 | apply refines_PM_LF |].
rewrite (proj1 PM_piecesLF_eq). exact (proj1 L_memF_wf). }
assert (HM2 : mem_ok tfibsegs E' (mrestrict (w_H W) (ms_mem ms)) L_memF).
{ apply (mem_ok_agree tfibsegs K_L E4); [| exact (proj1 (proj2 L_memF_wf)) | exact HM1].
split; [| subst E'; reflexivity]. intros j Hj. exact (Eold j Hj). }
unfold S_LF. rewrite <- PCL.
apply (st_ok_reabs tfibsegs LT162 E4 E' ss (restrict (w_H W) ms) L_regs L_memF L_facts HS).
- split; [| intros d _; subst E'; reflexivity]. intros j Hj. unfold LT162 in Hj. apply Nat.ltb_lt in Hj. exact (Eold j Hj).
- exact CHK.
- cbn [ms_regs restrict]. fold regs.
apply Forall_forall. intros [r j] Hin. vm_compute in Hin. cbn [fst snd].
Ltac onePF NEW i := rewrite <- (NEW i); [apply f_equal; reflexivity | cbn; lia | apply bv_eq; vm_compute; reflexivity].
repeat (destruct Hin as [Heq|Hin]; [injection Heq as <- <-;
first [ onePF NEW 0%nat | onePF NEW 1%nat | onePF NEW 2%nat | onePF NEW 3%nat | onePF NEW 4%nat | onePF NEW 5%nat | onePF NEW 6%nat | onePF NEW 7%nat
| onePF NEW 8%nat | onePF NEW 9%nat | onePF NEW 10%nat | onePF NEW 11%nat | onePF NEW 12%nat | onePF NEW 13%nat | onePF NEW 14%nat
| onePF NEW 15%nat | onePF NEW 16%nat | onePF NEW 17%nat
|   transitivity (getr regs 9%bv); [onePF NEW 1%nat | rewrite R9; rewrite <- R10; apply f_equal; apply bv_eq; vm_compute; reflexivity]
|   transitivity (getr regs 8%bv); [onePF NEW 0%nat | rewrite <- R8_11; apply f_equal; apply bv_eq; vm_compute; reflexivity] ] |]).
destruct Hin.
- rewrite L_fact_obls_eq.
constructor; [| constructor; [| constructor; [| constructor; [| constructor]]]];
unfold afact_ok; cbn [af_lo af_hi af_al2 fst snd fact_n fact_p fact_q fact_r]; rewrite ?V61, ?V62, ?V63, ?V65;
change (2 ^ 0) with 1; rewrite ?Z.mod_1_r; repeat split; try reflexivity; lia.
- exact HM2.
Qed.

(* ---- the program objects at the payload path's first call ---- *)
Lemma PL_IMG_E_in : forall (c0 : bool) k r, In r IMG_E -> In r (ss_mem (if c0 then S_PL0 else S_PL1 k)).
Proof.
intros c0 k r Hr. pose proof (PL_if c0 k) as (MPL & _). rewrite MPL, rsPL_split.
right. right. apply in_app_iff. right. exact Hr.
Qed.
Lemma PL_gf_start : forall (c0 : bool) k E (W : world tfibsegs) mem,
  mem_ok tfibsegs E (mrestrict (w_H W) mem) (ss_mem (if c0 then S_PL0 else S_PL1 k)) ->
  forall a, Exists (in_zr a) GF_OBJ ->
  aview tfibsegs (w_H W) mem a = Some (gf_init a) /\ writable_at tfibsegs (mrestrict (w_H W) mem) a.
Proof. intros c0 k E W mem HM. exact (img_gf_start _ E W mem HM (PL_IMG_E_in c0 k)). Qed.
End b.
