(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Theorem Labs, 2026-10: fuzz_preset image B' (asan-ubsan #102 pin d663f82d7f48), the walk of put: THE
   SHARED TAIL, from the seat at the join (index 65, `add s11, s3, s7`) to the return (index 115): the shadow checks of
   o and o + 8, len and buf loaded, the UBSan checks of buf + len (index 73 `bltu`, decided here by hand: buf + len
   does not wrap; index 77 decided by the engine from the facts buf >= 4096, len >= 0), __asan_memcpy (buf + len, s, n)
   (index 80, through its runtime row YGcallMxmn.aj_intrin_at_xm), the shadow checks of o + 8 and o again, len += n into
   the struct, buf + len + n named as its own atom (a zero-instruction stretch at index 90), the UBSan checks of
   buf + len + n (index 90 `bltu` by hand; 94 / 95 by the engine), the NUL store's shadow check from the destination's
   range_addressable, `sb zero`, the epilogue, the return. Its post gives the bytes: the copy, the NUL, the struct's
   fields, everything else below alloc_ceiling kept. GENERIC-P FORM: P on the start and the end memory.
   Port of the A walk S7a_put.v (sha256 f576f7636d50; internal record) put_tail; B' adds the UBSan checks and the re-checks.
   THE RE-HIDING MOVE (the texts' current form): on the grow arm the tail runs after fuzz_realloc, whose text
   concludes SRr' segs RZ_cf, so the tail's journal premise, its continuation's journal and its conclusion are at
   wle' segs RZ_cf (SRr' segs RZ_cf and the post fpostWR at wle'); the no-grow arm lifts its plain journal there. The
   runs use the runners over R (YC1fPx paj_run_x_invR / paj_run_to_x_invR, YSRrG.paj_branchR); __asan_memcpy is its
   rule over R (YGcallMxmn.aj_intrin_at_xmR, a plain SRr step lifted by YA0nH.SRr_SRrG), and so is the final ret.
   Numerals: indices DERIVED (PutB_Base.PK); 48 / 64 (after-call / stretch atom bands); 112 (LENGTH: put's frame);
   2147450879, 17594333495296, 140737479966720 (DERIVED: SHADOW_OFF - 1, kHighMemBeg + ... the two application bands);
   4096, 2 ^ 32, 2 ^ 47, 2 ^ 64 (DERIVED bounds). *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s YK0j.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn YP0b YP0a.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YN3v YI04 YI00 YG0s YP07.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YP0d YP0c YC80 YPsym YC4aP YC1fP YC81.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YM05 YI16 YK06 YImgTop YK1g.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YGcfNames YGcfRoomKeep YCbqG YC80x YC1fPx.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YCbqGcall YGcallMx YSRrMemnorm YCbqGcallW.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YAkMemnorm YGcallMxmn.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YA0nH YSRrG.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YGcfRehidePost.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B Require Import Listing_prog PAImg_prog PRH_ImgB.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import PRH_Base.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B.Prog Require Import PutB_Kit PutB_Base.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.

Section W. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {ci : CfImg} {cp : CfParams}.
Context {RL : PrhRoomLive}.
Context {SK : YI16.sink_head}.
#[local] Existing Instance prh_img_B.
Context {PA : PAImg B_prog_listing}.
#[local] Notation SEGS := (@pa_segs rc B_prog_listing PA).
#[local] Notation VAL := (@pa_val rc B_prog_listing PA).
#[local] Notation SIGMA := (@pa_sigma rc B_prog_listing PA).
#[local] Notation BASE := (@pa_val rc B_prog_listing PA A_TEXT).

Section h.
Variable B : asyms.
Variable ARx : alayout -> astate -> list Z -> world SEGS -> (word -> option byte) -> Model -> Prop.
Hypothesis PE : putb_env (SK := SK) B ARx.
Let LAWS : AR_laws_x SEGS B ARx cf_head := pe_laws B ARx PE.
#[local] Notation RZ := YGcfRehidePost.RZ_cf.
(* the runner and the branch over R at wle' segs RZ_cf (the whole tail is at that relation) *)
Let RUN := paj_run_xR (SK := SK) (PL := PL_prog_B) (PI := PA) B (@prh_pst prh_img_B) ARx LAWS
  (wle' SEGS RZ) (wle'_refl SEGS RZ) (wle'_trans SEGS RZ).
Let BR := paj_branchR (PI := PA) (wle' SEGS RZ).
Let RET := paj_ret_at (PL := PL_prog_B) (PI := PA).

(* the seat's shadow entry at any ARx state: the struct lies on the real stack, whose shadow is zero *)
Lemma putb_shok7 : forall (E' : env) ly S Hp (W : world SEGS) m md o,
  ARx ly S Hp W m md -> ew E' 23 = Z_to_bv 64 SHADOW_OFF -> ew E' 8 = Z_to_bv 64 o ->
  ly_stk_lo ly <= o -> o + 32 <= ly_stk_hi ly -> YM05.alloc_ceiling <= o -> o + 32 <= 2 ^ 47 ->
  sh_ok SEGS put_Bx7 put_SH7 E' (mrestrict (w_H W) m).
Proof.
intros E' ly S Hp W m md o HAR E23 E8 Hlo Hhi Ho0 Ho47.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
unfold sh_ok, put_SH7. constructor; [|constructor].
apply (shent_ok_of_range SEGS (w_H W) m E' put_Bx7 8 o 32 o 0 32).
- apply (put_stack_ra B ARx PE ly S Hp W m md o 32 HAR); lia.
- unfold U, put_Bx7. cbn [sv_denot]. rewrite E23, Z.add_0_r, Z_to_bv_bv_unsigned.
  rewrite unsigned_lit_small by (unfold SHADOW_OFF; lia). reflexivity.
- unfold U. cbn [sv_denot]. rewrite E8, Z.add_0_r, Z_to_bv_bv_unsigned. rewrite unsigned_lit_small by lia. reflexivity.
- lia.
- lia.
- intros a Ha. unfold SHADOW_OFF in *. lia.
Qed.

Lemma putb_tail : forall (P : (word -> option byte) -> Prop), srr_inv_laws SEGS P -> srr_inv_call SEGS P ->
  forall ly S Hp W regs mem md d o s n bufx len capx (FP : list (Z * Z))
    lyc Sc Hpc W1 (regs1 : bvmap 5 word) mem1 md1 k1
    (Qf : alayout -> astate -> list Z -> world SEGS -> bvmap 5 word -> (word -> option byte) -> Model -> Prop),
  ajournal_xR (SK := SK) SEGS B (@prh_pst prh_img_B) ARx (wle' SEGS RZ) (STK_put + d) (spZ regs + d) FP ly S Hp W mem md []
    lyc Sc Hpc W1 mem1 md1 k1 -> P mem1 ->
  YK0s.ret_ok (getr regs 1) -> getr regs 3 = w64 (as_gp B) -> getr regs 4 = w64 (as_tp B) ->
  spZ regs mod 16 = 0 -> 0 <= d -> d mod 16 = 0 -> spZ regs <= o -> o + 32 <= spZ regs + d -> o mod 8 = 0 ->
  spZ regs1 = spZ regs - 112 -> getr regs1 8 = Z_to_bv 64 o -> getr regs1 9 = Z_to_bv 64 n ->
  getr regs1 18 = Z_to_bv 64 s -> getr regs1 23 = Z_to_bv 64 SHADOW_OFF ->
  getr regs1 19 = Z_to_bv 64 (o / 8) -> getr regs1 22 = Z_to_bv 64 (o + 8) ->
  getr regs1 24 = Z_to_bv 64 (SHADOW_OFF + (o + 8) / 8) ->
  getr regs1 3 = getr regs 3 -> getr regs1 4 = getr regs 4 ->
  (forall j, (j < 13)%nat -> val_mem SEGS (mrestrict (w_H W1) mem1) (spZ regs - 8 - 8 * Z.of_nat j) 8
     (bv_unsigned (nth j (put_saved regs) (Z_to_bv 64 0)))) ->
  val_mem SEGS (mrestrict (w_H W1) mem1) o 8 bufx -> val_mem SEGS (mrestrict (w_H W1) mem1) (o + 8) 8 len ->
  val_mem SEGS (mrestrict (w_H W1) mem1) (o + 16) 8 capx -> val_mem SEGS (mrestrict (w_H W1) mem1) (o + 24) 4 0 ->
  0 <= capx < 2 ^ 64 -> 0 <= len ->
  (forall a, spZ regs <= a < spZ regs + d -> ~ inFP FP a -> aview SEGS (w_H W1) mem1 a = aview SEGS (w_H W) mem a) ->
  (forall a, o <= a < o + 32 -> inFP FP a) ->
  0 <= n < 2 ^ 32 -> 4096 <= bufx -> bufx + len + n + 1 <= YM05.alloc_ceiling ->
  amem_range (bufx + len) (n + 1) ->
  (forall a, bufx + len <= a <= bufx + len + n ->
     awr_byte (STK_put + d) (spZ regs + d) FP (ablocks B ly S) (ablocks B lyc Sc) lyc [] a) ->
  range_addressable (aview SEGS (w_H W1) mem1) SHADOW_OFF (bufx + len) (n + 1) ->
  (0 < n -> shadow_hull_vis (aview SEGS (w_H W1) mem1) (bufx + len) n) ->
  4096 <= s -> s + n <= YM05.alloc_ceiling -> amem_range s n ->
  (forall a, s <= a < s + n -> aview SEGS (w_H W1) mem1 a <> None) ->
  (bufx + len + n <= s \/ s + n <= bufx + len) ->
  range_addressable (aview SEGS (w_H W1) mem1) SHADOW_OFF s n ->
  (0 < n -> shadow_hull_vis (aview SEGS (w_H W1) mem1) s n) ->
  (forall regs' mem' md' k',
     ajournal_xR (SK := SK) SEGS B (@prh_pst prh_img_B) ARx (wle' SEGS RZ) (STK_put + d) (spZ regs + d) FP ly S Hp W mem md []
       lyc Sc Hpc W1 mem' md' k' -> P mem' ->
     (forall a, 0 <= a < YM05.alloc_ceiling -> ~ (bufx + len <= a <= bufx + len + n) ->
        aview SEGS (w_H W1) mem' a = aview SEGS (w_H W1) mem1 a) ->
     (forall i, 0 <= i < n -> aview SEGS (w_H W1) mem' (bufx + len + i) = aview SEGS (w_H W1) mem1 (s + i)) ->
     aview SEGS (w_H W1) mem' (bufx + len + n) = Some 0 ->
     val_mem SEGS (mrestrict (w_H W1) mem') o 8 bufx ->
     val_mem SEGS (mrestrict (w_H W1) mem') (o + 8) 8 (len + n) ->
     val_mem SEGS (mrestrict (w_H W1) mem') (o + 16) 8 capx ->
     val_mem SEGS (mrestrict (w_H W1) mem') (o + 24) 4 0 ->
     Qf lyc Sc Hpc W1 regs' mem' md') ->
  SRr' SEGS RZ W1 (mkCfg (YK11.mkst regs1 (Z_to_bv 64 (BASE + PK 65)) mem1 (YK11.seg_rom SEGS)) md1)
    (fpostWR B ARx SK (wle' SEGS RZ) STK_put d FP regs ly S Hp W mem md Qf).
Proof.
intros P PLAW PCALL.
pose (RUNI := paj_run_x_invR (SK := SK) (PL := PL_prog_B) (PI := PA) B (@prh_pst prh_img_B) ARx LAWS P PLAW
  (wle' SEGS RZ) (wle'_refl SEGS RZ) (wle'_trans SEGS RZ)).
pose (RUNTOI := paj_run_to_x_invR (SK := SK) (PL := PL_prog_B) (PI := PA) B (@prh_pst prh_img_B) ARx LAWS P PLAW
  (wle' SEGS RZ) (wle'_refl SEGS RZ) (wle'_trans SEGS RZ)).
intros ly S Hp W regs mem md d o s n bufx len capx FP lyc Sc Hpc W1 regs1 mem1 md1 k1 Qf
  HJ HPM Hra Hgp Htp Hal16 Hd0 Hd16 Hol Hoh Ho8 Hsp1 R8 R9 R18 R23 R19 R22 R24 R3 R4 Hsv Vb Vl Vc Vf Rc Rl HWK HFPo
  Hn Hb4096 Hbc Hamr Hawr Hra_d Hhull_d Hs4096 Hsc Hamrs Hsvis Hdisj Hra_s Hhull_s HQ.
unfold SRr'.
pose proof HJ as (HAR1 & Hly1 & _ & Hwle1 & _ & _ & _ & Hk1 & _ & _ & _ & _ & _ & Hpres1 & Hstat1 & _).
pose proof Hstat1 as (Hal1 & Hstk01 & Hceil1 & Hslo1 & Hshi1 & H471 & Hbot1 & Htop1 & Htop21).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof (@alloc_ceiling_value rc) as HCV.
assert (HKs : 112 + 4096 + 16 <= STK_put) by (vm_compute; discriminate).
assert (Hes : ESTACK = 4096) by reflexivity.
assert (Ho64 : bv_unsigned (getr regs1 8) = o) by (rewrite R8; apply unsigned_lit_small; lia).
(* the struct's 32 bytes are on the stack: their shadow is zero *)
pose proof Hly1 as (_ & _ & _ & _ & _ & _ & _ & _ & Etop1 & Eslo1 & Eshi1 & _).
assert (Hora : range_addressable (aview SEGS (w_H W1) mem1) SHADOW_OFF o 32)
  by (apply (put_stack_ra B ARx PE lyc Sc Hpc W1 mem1 md1 o 32 HAR1); rewrite ?Eslo1, ?Eshi1; lia).
destruct (put_seat (PK 65) W1 regs regs1 mem1 bufx len capx n) as (HS & SHOK).
{ rewrite Hsp1, Zminus_mod, Hal16. reflexivity. }
{ rewrite Hsp1. lia. }
{ rewrite Hsp1, Ho64. lia. }
{ intros j Hj. rewrite Hsp1. replace (spZ regs - 112 + 104 - 8 * Z.of_nat j) with (spZ regs - 8 - 8 * Z.of_nat j) by lia.
  exact (Hsv j Hj). }
{ rewrite Ho64. exact Ho8. }
{ rewrite Ho64. lia. }
{ intros a Ha. rewrite Ho64 in Ha. apply Hpres1. lia. }
{ rewrite Ho64. exact Vb. }
{ lia. }
{ rewrite Ho64. exact Vl. }
{ lia. }
{ rewrite Ho64. exact Vc. }
{ exact Rc. }
{ rewrite Ho64. exact Vf. }
{ exact R23. }
{ exact R9. }
{ lia. }
{ rewrite Ho64. exact R19. }
{ rewrite Ho64. exact R22. }
{ rewrite Ho64. exact R24. }
{ rewrite Ho64. exact Hora. }
set (xs := [Z_to_bv 64 bufx; Z_to_bv 64 len; Z_to_bv 64 capx] ++ put_saved regs) in *.
set (E := put_Es regs1 regs bufx len capx) in *.
assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (EL : forall kk, (kk < A_TEXT)%nat -> ew E kk = ew (Ereg regs1 xs) kk)
  by (intros kk Hk; subst E; unfold put_Es; apply Eimg_low; exact Hk).
assert (EG : forall (kk : nat) (r : bv 5), (kk < 32)%nat -> Z.of_nat kk = bv_unsigned r -> ew E kk = getr regs1 r)
  by (intros kk r Hk Hr; rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs1 _ kk r Hr)).
assert (Usp : bv_unsigned (ew E 2) = spZ regs - 112) by (rewrite (EG 2%nat 2%bv) by (lia || reflexivity); exact Hsp1).
assert (Uo : bv_unsigned (ew E 8) = o) by (rewrite (EG 8%nat 8%bv) by (lia || reflexivity); exact Ho64).
assert (EX : forall j, (j < 16)%nat -> ew E (32 + j) = nth j xs (Z_to_bv 64 0))
  by (intros j Hj; rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs1 xs j)).
assert (E32 : ew E 32 = Z_to_bv 64 bufx) by exact (EX 0%nat ltac:(lia)).
assert (E33 : ew E 33 = Z_to_bv 64 len) by exact (EX 1%nat ltac:(lia)).
assert (E34 : ew E 34 = Z_to_bv 64 capx) by exact (EX 2%nat ltac:(lia)).
assert (U32 : bv_unsigned (ew E 32) = bufx) by (rewrite E32; apply unsigned_lit_small; lia).
assert (U33 : bv_unsigned (ew E 33) = len) by (rewrite E33; apply unsigned_lit_small; lia).
(* ---- run 1: indices 65 .. 73, the two shadow checks, len and buf, the UBSan check of buf + len ---- *)
paj_run_tok_x_inv RUNI HS HJ SHOK HPM put_Bspan.
{ put_awr. }
psrr_branch_tok RUN BR HS SHOK put_Bspan.
all: match goal with Hb : branch_taken _ _ _ = _ |- _ => rename Hb into Hc end.
all: rewrite branch_ltu_U, U_add_off_atom, U_SOff, U32, U33 in Hc
  by (rewrite ?U32, ?U33; unfold M64; lia).
all: rewrite Z.add_0_r, zcanon_id in Hc by (unfold M64; lia).
(* taken: buf + len < buf, impossible *)
1: (exfalso; apply Z.ltb_lt in Hc; lia).
apply Z.ltb_ge in Hc.
(* ---- run 1b: indices 73 .. 80, the engine's check of index 77, a1 := s, a2 := n, the __asan_memcpy call ---- *)
paj_run_tok_x_inv RUNI HS HJ SHOK HPM put_Bspan.
{ put_awr. }
pmkst HS.
prreg HS (10%bv : bv 5) Q10. prreg HS (11%bv : bv 5) Q11. prreg HS (12%bv : bv 5) Q12.
prreg HS (1%bv : bv 5) Q1. prreg HS (2%bv : bv 5) Q2. prreg HS (3%bv : bv 5) Q3. prreg HS (4%bv : bv 5) Q4.
(* the two runs write nothing (the seat's write window, the struct, is untouched by loads) *)
assert (KA : forall a, 0 <= a < 2 ^ 64 -> ~ (o <= a < o + 32) ->
  aview SEGS (w_H W1) (ms_mem ms0) a = aview SEGS (w_H W1) mem1 a).
{ intros a Ha Hn'. apply aview_eq_of. rewrite (HFr0 (Z_to_bv 64 a)), (HFr (Z_to_bv 64 a)); [reflexivity | |];
  rewrite unsigned_lit_small by lia; intros (r & Hr & Hra');
  match type of Hr with In _ ?rs => let v := eval vm_compute in rs in change rs with v in Hr end;
  repeat (destruct Hr as [<- | Hr];
    [cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hra'; rewrite ?Usp, ?Uo in Hra'; lia | ]);
  destruct Hr. }
clear HF HG HFr HF0 HG0 HFr0.
(* ---- the copy: __asan_memcpy (bufx + len, s, n) through its runtime row, by the rule over R at wle' segs RZ_cf (a plain
   SRr step, lifted) ---- *)
eapply (SRrG_bind SEGS (wle' SEGS RZ) (wle'_trans SEGS RZ)).
{ apply (SRr_SRrG SEGS (wle' SEGS RZ) (wle_wle' SEGS RZ)).
  lazymatch goal with |- SRr _ _ (mkCfg (mkst ?rT _ ?mT _) ?dT) _ =>
  eapply (YGcallMxmn.aj_intrin_at_xmR (SK := SK) SEGS B (@prh_pst prh_img_B) ARx LAWS (@pa_segs_low _ _ PA)
    (wle' SEGS RZ) OCpy (SIGMA AS___asan_memcpy) (pe_amc B ARx PE) W1 rT mT (STK_put + d) (spZ regs + d) FP ly S Hp W
    mem md [] lyc Sc Hpc dT k1 (bufx + len) s n (- (112 + d)) _ HJ) end.
  - rewrite Q10, E32, E33, alu_add_small by (unfold M64; lia). reflexivity.
  - rewrite Q11, (EG 18%nat 18%bv) by (lia || reflexivity). rewrite R18. reflexivity.
  - rewrite Q12, (EG 9%nat 9%bv) by (lia || reflexivity). rewrite R9. reflexivity.
  - lia.
  - lia.
  - lia.
  - unfold spZ at 1. rewrite Q2. change (bv_unsigned (ew E 2) = spZ regs + d + - (112 + d)). lia.
  - replace (- (112 + d)) with ((- 7 - d / 16) * 16) by (pose proof (Z.div_mod d 16 ltac:(lia)); lia).
    apply Z_mod_mult.
  - lia.
  - rewrite Hes. lia.
  - rewrite Q3, (EG 3%nat 3%bv) by (lia || reflexivity). rewrite R3. exact Hgp.
  - rewrite Q4, (EG 4%nat 4%bv) by (lia || reflexivity). rewrite R4. exact Htp.
  - exact Q1.
  - apply (ret_ok_codeptr_v (PI := PA)); [lia | reflexivity].
  - intros a Ha. split; [apply Hawr; lia | rewrite Hes; lia].
  - unfold amem_range in *. lia.
  - eapply (range_addressable_agree (aview SEGS (w_H W1) mem1)).
    { intros x Hx. pose proof (put_shadow_low x ltac:(lia)). apply KA; lia. }
    apply (range_addressable_sub _ _ (bufx + len) (n + 1)); [exact Hra_d | lia | lia].
  - intros Hn0 s0 Hs0. pose proof (put_hull_low (bufx + len) n s0 ltac:(lia) Hn0 ltac:(lia) Hs0).
    rewrite KA by lia. exact (Hhull_d Hn0 s0 Hs0).
  - split; [lia|]. split; [lia|]. split.
    { intros a Ha. split; [rewrite KA by lia; exact (Hsvis a Ha)|].
      unfold spZ at 1 2. rewrite Q2. change (bv_unsigned (ew E 2)) with (bv_unsigned (ew E 2)). rewrite Usp, Hes. lia. }
    split; [exact Hdisj|]. split; [exact Hamrs|]. split.
    + eapply (range_addressable_agree (aview SEGS (w_H W1) mem1)); [|exact Hra_s].
      intros x Hx. pose proof (put_shadow_low x ltac:(lia)). apply KA; lia.
    + intros Hn0 s0 Hs0. pose proof (put_hull_low s n s0 ltac:(lia) Hn0 ltac:(lia) Hs0).
      rewrite KA by lia. exact (Hhull_s Hn0 s0 Hs0). }
cbv beta. intros W5 c5 _ (-> & regs2 & mem2 & md2 & -> & HJ2 & HP2 & Ha02 & Hcopy & Hfr2 & Hpres2 & Hmn2).
(* P crosses the copy by the row's keep *)
pose proof (PCALL _ _ Hmn2 HPM) as HPM2. clear HPM Hmn2. rename HPM2 into HPM.
cbv beta iota in Hcopy.
pose proof HJ2 as (HAR2 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres2J & Hstat2 & _).
pose proof Hstat2 as (_ & _ & _ & Hslo2 & Hshi2 & _).
jafter_call_keep_pi HS 48%nat regs2 (mrestrict (w_H W1) mem2) HP2 [0; 1]%nat HSX.
lazymatch type of HSX with ?T -> _ => assert (HRKX : T) end.
{ constructor; [|constructor; [|apply Forall_nil]]; split.
  - intros a Ha. cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val] in Ha. rewrite Usp in Ha.
    apply (mbyte_of_aview SEGS). apply Hfr2; [lia | lia | rewrite Hes; lia].
  - intros a Ha _. cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha. lia.
  - intros a Ha. cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val] in Ha. rewrite Uo in Ha.
    apply (mbyte_of_aview SEGS). apply Hfr2; [lia | lia | rewrite Hes; lia].
  - intros a Ha _. cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha. rewrite Uo in Ha.
    apply (apresent_writable SEGS). apply Hpres2J. lia. }
specialize (HSX HRKX). clear HRKX. rewrite <- restrict_mkst_fx in HSX.
remember (havoc E 48 (map (getr regs2) CLOB)) as E2 eqn:HE2 in HSX.
assert (HEI2 : img_env VAL A_LIM E2) by (rewrite HE2; apply img_env_havoc; [exact HEI | cbv; lia]).
assert (OLD2 : forall kk, (kk < 48)%nat -> ew E2 kk = ew E kk) by (intros kk Hk; rewrite HE2; apply ew_havoc_old; exact Hk).
clear HE2.
assert (Usp2 : bv_unsigned (ew E2 2) = spZ regs - 112) by (rewrite OLD2 by lia; exact Usp).
assert (Uo2 : bv_unsigned (ew E2 8) = o) by (rewrite OLD2 by lia; exact Uo).
assert (SHOK2 : sh_ok SEGS put_Bx7 put_SH7 E2 (mrestrict (w_H W1) mem2)).
{ apply (putb_shok7 E2 lyc Sc Hpc W1 mem2 md2 o HAR2).
  - rewrite OLD2 by lia. rewrite (EG 23%nat 23%bv) by (lia || reflexivity). exact R23.
  - rewrite OLD2 by lia. rewrite (EG 8%nat 8%bv) by (lia || reflexivity). exact R8.
  - rewrite ?Eslo1; lia.
  - rewrite ?Eshi1; lia.
  - lia.
  - lia. }
clear HS SHOK HJ HEI. rename HSX into HS. rename SHOK2 into SHOK. rename HJ2 into HJ. rename HEI2 into HEI.
(* ---- run 2: indices 81 .. 89, the shadow checks of o + 8 and o, len + n into the struct, a0 = buf + len + n ---- *)
paj_run_to_tok_x_inv RUNTOI HS HJ SHOK HPM put_Bspan (PK 90).
all: try solve [put_awr].
rename HFr into HFr2. clear HF HG.
lazymatch type of HS with st_ok_pi _ _ _ _ (restrict _ ?X) => rename X into MS2 end.
assert (KB2 : forall a, 0 <= a < 2 ^ 64 -> ~ (o <= a < o + 32) ->
  aview SEGS (w_H W1) (ms_mem MS2) a = aview SEGS (w_H W1) mem2 a).
{ intros a Ha Hn'. apply aview_eq_of. rewrite (HFr2 (Z_to_bv 64 a)); [reflexivity|].
  rewrite unsigned_lit_small by lia. intros (r & Hr & Hra').
  match type of Hr with In _ ?rs => let v := eval vm_compute in rs in change rs with v in Hr end.
  repeat (destruct Hr as [<- | Hr];
    [cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hra'; rewrite ?Usp2, ?Uo2 in Hra'; lia | ]).
  destruct Hr. }
pmkst HS.
prreg HS (10%bv : bv 5) R10.
set (X := bufx + len + n) in *.
assert (HX10 : getr (ms_regs MS2) 10 = Z_to_bv 64 X).
{ rewrite R10. rewrite ?(OLD2 9%nat), ?(OLD2 32%nat), ?(OLD2 33%nat) by lia.
  rewrite ?(EG 9%nat 9%bv) by (lia || reflexivity).
  rewrite ?R9, ?E32, ?E33.
  repeat rewrite alu_add_small by (unfold M64; lia).
  subst X. f_equal. lia. }
(* the NUL store's address bufx + len + n: an atom of its own (a zero-instruction stretch that clobbers only a0), so
   the engine decides index 90's comparison partner, the checks 94 / 95, the NUL byte's shadow check and its region *)
let v := eval vm_compute in (PK 90) in
jafter_stretch_pi HS 64%nat (ms_regs MS2) (mrestrict (w_H W1) (ms_mem MS2)) ([10%bv] : list (bv 5)) v HSY.
specialize (HSY (fun r _ => eq_refl)).
lazymatch type of HSY with ?T -> _ => assert (HKY : T) end.
{ apply Forall_forall. intros r _. split; [intros a _; reflexivity | intros a _ Hw; exact Hw]. }
specialize (HSY HKY). clear HKY. rewrite <- restrict_mkst_fx in HSY.
remember (havoc E2 64 (map (getr (ms_regs MS2)) [10%bv])) as E3 eqn:HE3 in HSY.
assert (HEI3 : img_env VAL A_LIM E3) by (rewrite HE3; apply img_env_havoc; [exact HEI | cbv; lia]).
assert (OLD3 : forall kk, (kk < 64)%nat -> ew E3 kk = ew E2 kk) by (intros kk Hk; rewrite HE3; apply ew_havoc_old; exact Hk).
assert (E3X : ew E3 64 = Z_to_bv 64 X) by (rewrite HE3, <- HX10; reflexivity).
clear HE3.
assert (Usp3 : bv_unsigned (ew E3 2) = spZ regs - 112) by (rewrite OLD3 by lia; exact Usp2).
assert (Uo3 : bv_unsigned (ew E3 8) = o) by (rewrite OLD3 by lia; exact Uo2).
assert (UX3 : bv_unsigned (ew E3 64) = X) by (rewrite E3X; apply unsigned_lit_small; subst X; lia).
assert (U32b : bv_unsigned (ew E3 32) = bufx) by (rewrite OLD3, OLD2 by lia; exact U32).
assert (HXP : apresent (w_H W1) (ms_mem MS2) X /\ ~ aowned B lyc Sc X).
{ eapply (awr_byte_present_xR (SK := SK) SEGS B (@prh_pst prh_img_B) ARx LAWS (wle' SEGS RZ)).
  all: first [exact HJ | exact (@pa_segs_low _ _ PA) | apply Hawr; subst X; lia]. }
(* the NUL byte is application memory, low or high (amem_range): its atom's range is the band it lies in, from
   bufx >= 4096 up *)
assert (HXr : X + 1 <= SHADOW_OFF \/ SHADOW_OFF + 2 ^ 44 <= X).
{ unfold amem_range in Hamr. subst X. unfold SHADOW_OFF. rewrite C3, C5 in Hamr. lia. }
destruct HXr as [HXr | HXr].
1: pose proof (st_ok_pi_add_fact E3 _ _ 64%nat (mkAF 4096 2147450879 0) HSY) as HSF.
2: pose proof (st_ok_pi_add_fact E3 _ _ 64%nat (mkAF 17594333495296 140737479966720 0) HSY) as HSF.
all: lazymatch type of HSF with ?T -> _ => assert (HAF : T)
  by (unfold afact_ok; cbn [af_lo af_hi af_al2]; rewrite UX3, Z.pow_0_r, Z.mod_1_r; subst X; unfold SHADOW_OFF in *; lia) end.
all: specialize (HSF HAF); clear HAF.
all: pose proof (st_ok_pi_add_region E3 _ _ (YP09.mkRegion (Some 64%nat) 0 1 0 1 []) HSF ltac:(vm_compute; reflexivity)) as HSR.
all: lazymatch type of HSR with ?A -> ?B -> _ =>
  assert (HA : A) by (unfold region_ok; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val ms_mem restrict mkst];
    rewrite UX3; split; [lia|]; split; [lia|]; split; [|constructor];
    intros oo Hoo; apply (apresent_writable SEGS); replace (X + oo) with X by lia; exact (proj1 HXP));
  assert (HB : B) by (lazymatch goal with |- all_disjoint _ _ (ss_mem ?s) => let rs := eval vm_compute in (ss_mem s) in change (ss_mem s) with rs end;
    cbn [all_disjoint]; unfold extent_disjoint; cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val]; rewrite UX3, Usp3, Uo3; subst X; lia);
  specialize (HSR HA HB); clear HA HB end.
all: assert (SHOK3 : sh_ok SEGS put_Bx7 put_SH7 E3 (mrestrict (w_H W1) (ms_mem MS2)))
  by (apply (putb_shok7 E3 lyc Sc Hpc W1 (ms_mem MS2) _ o (proj1 HJ));
        [ rewrite OLD3, OLD2 by lia; rewrite (EG 23%nat 23%bv) by (lia || reflexivity); exact R23
        | rewrite OLD3, OLD2 by lia; rewrite (EG 8%nat 8%bv) by (lia || reflexivity); exact R8
        | rewrite ?Eslo1; lia | rewrite ?Eshi1; lia | lia | lia ]).
all: clear HS HSY HSF SHOK HEI; rename HSR into HS; rename SHOK3 into SHOK; rename HEI3 into HEI.
(* ---- index 90: the UBSan check of buf + len + n, by hand: X >= bufx ---- *)
all: psrr_branch_tok RUN BR HS SHOK put_Bspan.
all: match goal with Hb : branch_taken _ _ _ = _ |- _ => rename Hb into Hc90 end.
all: rewrite branch_ltu_U, (U_atom E3 64 X E3X), (U_atom E3 32 bufx) in Hc90
  by (first [subst X; lia | rewrite OLD3, OLD2 by lia; exact E32 | lia]).
all: try solve [exfalso; apply Z.ltb_lt in Hc90; subst X; lia].
all: apply Z.ltb_ge in Hc90.
(* ---- run 3: indices 90 .. 115, the checks 94 / 95, the NUL byte's shadow check, sb zero, the epilogue, the return ---- *)
all: paj_run_tok_x_inv RUNI HS HJ SHOK HPM put_Bspan.
all: try solve [ lazymatch goal with |- awr_ok ?Ex ?rs ?stk ?sp0' ?fp ?b0 ?bc ?ly' ?own' =>
    let rs' := eval vm_compute in rs in change (awr_ok Ex rs' stk sp0' fp b0 bc ly' own') end;
  eapply (awr_ok_cons_gen E3 _ _ _ _ _ _ _ _ _ 64%nat X); [reflexivity | exact UX3 | | put_awr];
  intros a Ha; cbn [YP09.r_wlo YP09.r_whi] in Ha; apply Hawr; subst X; lia ].
(* the NUL byte's shadow check: the destination's range_addressable at the seat, kept by run 1 (no write), the copy
   (writes the destination and its ESTACK window) and run 2 (the struct only) *)
all: try solve [ lazymatch goal with |- context [rd_of ?SG (mrestrict ?HH (ms_mem ?MM))] =>
      change (rd_of SG (mrestrict HH (ms_mem MM))) with (aview SG HH (ms_mem MM)) end;
  cbn [ms_mem mkst]; unfold put_Bx7;
  rewrite (U_atom E3 23%nat SHADOW_OFF) by (first [ unfold SHADOW_OFF; lia
    | rewrite OLD3, OLD2 by lia; rewrite (EG 23%nat 23%bv) by (lia || reflexivity); exact R23 ]);
  rewrite (U_atom E3 64%nat X E3X) by (subst X; lia);
  eapply (range_addressable_agree (aview SEGS (w_H W1) mem1));
  [ intros x Hx; pose proof (put_shadow_low x ltac:(subst X; lia)) as Hsl;
    unfold shadow_of_addr, SHADOW_OFF in Hsl |- *;
    unfold amem_range in Hamr; rewrite C3, C5 in Hamr;
    set (q := x / 8) in *; assert (0 <= q) by (unfold q; apply Z.div_pos; lia);
    assert (8 * q <= x) by (unfold q; apply Z.mul_div_le; lia); clearbody q;
    rewrite (KB2 (2147450880 + q)) by lia;
    rewrite (Hfr2 (2147450880 + q)); [rewrite KA by lia; reflexivity | lia | subst X; lia | rewrite Hes; lia]
  | apply (range_addressable_sub _ _ (bufx + len) (n + 1)); [exact Hra_d | subst X; lia | subst X; lia] ] ].
(* ---- the return at index 115 and the post ---- *)
all: lazymatch type of HS with st_ok_pi _ _ _ _ (restrict _ ?XX) => rename XX into MSF end.
all: assert (KC3 : forall a, 0 <= a < 2 ^ 64 -> a <> X -> ~ (o <= a < o + 32) ->
  aview SEGS (w_H W1) (ms_mem MSF) a = aview SEGS (w_H W1) (ms_mem MS2) a)
  by (intros a Ha HaX Hn'; apply aview_eq_of; rewrite (HFr (Z_to_bv 64 a)); [reflexivity|];
      rewrite unsigned_lit_small by lia; intros (r & Hr & Hra');
      match type of Hr with In _ ?rs => let v := eval vm_compute in rs in change rs with v in Hr end;
      repeat (destruct Hr as [<- | Hr];
        [cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hra'; rewrite ?UX3, ?Usp3, ?Uo3 in Hra'; lia | ]);
      destruct Hr).
all: assert (KLOW : forall a, 0 <= a < YM05.alloc_ceiling -> ~ (bufx + len <= a <= X) ->
  aview SEGS (w_H W1) (ms_mem MSF) a = aview SEGS (w_H W1) mem1 a)
  by (intros a Ha Hn'; subst X; rewrite KC3 by lia; rewrite KB2 by lia;
      rewrite (Hfr2 a) by (rewrite ?Hes; lia); apply KA; lia).
all: assert (KWIN : forall a, spZ regs <= a < 2 ^ 64 -> ~ (o <= a < o + 32) ->
  aview SEGS (w_H W1) (ms_mem MSF) a = aview SEGS (w_H W1) mem1 a)
  by (intros a Ha Hn'; subst X; rewrite KC3 by lia; rewrite KB2 by lia;
      rewrite (Hfr2 a) by (rewrite ?Hes; lia); apply KA; lia).
all: try rewrite wvb_collapse in HJ.
all: apply (SRr_SRrG SEGS (wle' SEGS RZ) (wle_wle' SEGS RZ)).
all: apply (RET W1 _ _ _ _ _ HS eq_refl ltac:(vm_compute; reflexivity)); intros matF.
all: lazymatch type of HS with st_ok_pi _ _ ?Ef _ _ => set (EF := Ef) in HS end.
all: assert (EFo : forall kk, (kk < 48)%nat -> ew EF kk = ew E kk)
  by (intros kk Hk; subst EF; rewrite !ew_ewset_other by lia; rewrite OLD3, OLD2 by lia; reflexivity).
all: assert (SAV : forall j, (j < 13)%nat -> ew EF (35 + j) = nth j (put_saved regs) (Z_to_bv 64 0))
  by (intros j Hj; rewrite EFo by lia; replace (35 + j)%nat with (32 + (3 + j))%nat by lia;
      rewrite EX by lia; subst xs; rewrite app_nth2 by (cbn [length]; lia);
      replace (3 + j - length [Z_to_bv 64 bufx; Z_to_bv 64 len; Z_to_bv 64 capx])%nat with j by (cbn [length]; lia);
      reflexivity).
all: assert (GR : forall rr : bv 5, getr (ms_regs MSF) rr = sv_denot EF (sr_get (ss_regs _) rr))
  by (intros rr; exact (st_ok_pi_restrict_reg (w_H W1) EF _ MSF rr HS)).
all: assert (D0 : forall (kx : nat) (wx : word), ew EF kx = wx -> sv_denot EF (SOff kx 0) = wx)
  by (intros kx wx Hk; cbn [sv_denot]; rewrite Hk, Z.add_0_r; apply Z_to_bv_bv_unsigned).
all: assert (HP : aregs_preserved regs (ms_regs MSF)) by (intros r Hr; unfold acallee_saved in Hr;
  assert (Hr' : r = 2 \/ r = 3 \/ r = 4 \/ r = 8 \/ r = 9 \/ r = 18 \/ r = 19 \/ r = 20 \/ r = 21 \/ r = 22 \/
                r = 23 \/ r = 24 \/ r = 25 \/ r = 26 \/ r = 27) by lia;
  rewrite GR;
  repeat destruct Hr' as [-> | Hr']; try (subst r);
  match goal with |- sv_denot ?EE ?e = _ => let v := eval vm_compute in e in change e with v end;
  first
    [ (cbn [sv_denot]; rewrite EFo, Usp by lia; rewrite Z.sub_add; apply Z_to_bv_bv_unsigned)
    | (apply D0; rewrite EFo by lia; rewrite (EG 3%nat 3%bv) by (lia || reflexivity); exact R3)
    | (apply D0; rewrite EFo by lia; rewrite (EG 4%nat 4%bv) by (lia || reflexivity); exact R4)
    | (apply D0; first [ exact (SAV 1%nat ltac:(lia)) | exact (SAV 2%nat ltac:(lia)) | exact (SAV 3%nat ltac:(lia))
        | exact (SAV 4%nat ltac:(lia)) | exact (SAV 5%nat ltac:(lia)) | exact (SAV 6%nat ltac:(lia))
        | exact (SAV 7%nat ltac:(lia)) | exact (SAV 8%nat ltac:(lia)) | exact (SAV 9%nat ltac:(lia))
        | exact (SAV 10%nat ltac:(lia)) | exact (SAV 11%nat ltac:(lia)) | exact (SAV 12%nat ltac:(lia)) ]) ]).
all: assert (Hra1 : getr (ms_regs MSF) 1 = getr regs 1)
  by (rewrite GR; match goal with |- sv_denot ?EE ?e = _ => let v := eval vm_compute in e in change e with v end;
      apply D0; exact (SAV 0%nat ltac:(lia))).
all: assert (UoF : bv_unsigned (ew EF 8) = o) by (rewrite EFo by lia; exact Uo).
all: assert (UXF : bv_unsigned (ew EF 64) = X) by (subst EF; rewrite !ew_ewset_other by lia; exact UX3).
(* the struct's fields and the NUL byte at the end, from the final state's regions *)
all: put_region HS 2%nat (YP09.mkRegion (Some 8%nat) 0 32 0 32
  [ YP09.mkChunk 8 (CVal 8 (SAlu ALU_ADD (SOff 9 0) (SOff 33 0))); YP09.mkChunk 0 (CVal 8 (SOff 32 0));
    YP09.mkChunk 16 (CVal 8 (SOff 34 0)); YP09.mkChunk 24 (CVal 4 (SLit 0)) ]) HRS.
all: put_region HS 0%nat (YP09.mkRegion (Some 64%nat) 0 1 0 1 [ YP09.mkChunk 0 (CVal 1 (SLit 0)) ]) HRX.
all: assert (W0' : val_mem SEGS (mrestrict (w_H W1) (ms_mem MSF)) o 8 bufx)
  by (pose proof (field_of_region SEGS EF _ 8 o _ 0 32 0 32 0 8%N (SOff 32 0) bufx HRS UoF ltac:(cbn; tauto)
        ltac:(apply D0; rewrite EFo by lia; exact E32) ltac:(cbn; lia) ltac:(cbn; lia)) as Hv;
      rewrite Z.add_0_r in Hv; exact Hv).
all: assert (W8' : val_mem SEGS (mrestrict (w_H W1) (ms_mem MSF)) (o + 8) 8 (len + n))
  by (exact (field_of_region SEGS EF _ 8 o _ 0 32 0 32 8 8%N (SAlu ALU_ADD (SOff 9 0) (SOff 33 0)) (len + n) HRS UoF
        ltac:(cbn; tauto)
        ltac:(cbn [sv_denot]; rewrite !Z.add_0_r, !Z_to_bv_bv_unsigned; rewrite (EFo 9%nat), (EFo 33%nat) by lia;
              rewrite (EG 9%nat 9%bv) by (lia || reflexivity); rewrite R9, E33;
              rewrite alu_add_small by (unfold M64; lia); f_equal; lia)
        ltac:(cbn; lia) ltac:(cbn; lia))).
all: assert (W16' : val_mem SEGS (mrestrict (w_H W1) (ms_mem MSF)) (o + 16) 8 capx)
  by (exact (field_of_region SEGS EF _ 8 o _ 0 32 0 32 16 8%N (SOff 34 0) capx HRS UoF ltac:(cbn; tauto)
        ltac:(apply D0; rewrite EFo by lia; exact E34) ltac:(cbn; lia) ltac:(cbn; lia))).
all: assert (W24' : val_mem SEGS (mrestrict (w_H W1) (ms_mem MSF)) (o + 24) 4 0)
  by (exact (field_of_region SEGS EF _ 8 o _ 0 32 0 32 24 4%N (SLit 0) 0 HRS UoF ltac:(cbn; tauto)
        eq_refl ltac:(cbn; lia) ltac:(cbn; lia))).
all: assert (WX : aview SEGS (w_H W1) (ms_mem MSF) X = Some 0)
  by (apply put_aview_val1;
      pose proof (field_of_region SEGS EF _ 64 X _ 0 1 0 1 0 1%N (SLit 0) 0 HRX UXF ltac:(cbn; tauto)
        eq_refl ltac:(cbn; lia) ltac:(cbn; lia)) as Hv;
      rewrite Z.add_0_r in Hv; exact Hv).
all: unfold fpostWR.
all: lazymatch goal with |- exists _ _ _ _ _ _ _, mkCfg (mkst ?r _ ?m _) ?dd = _ /\ _ =>
  exists lyc, Sc, Hpc, r, m, dd, k1 end.
all: split; [rewrite Hra1; unfold YK0s.ret_ok in Hra; rewrite Hra; reflexivity|].
all: split; [exact (ajournal_x_materializeR (SK := SK) SEGS B (@prh_pst prh_img_B) ARx LAWS (@pa_segs_low _ _ PA)
  (wle' SEGS RZ) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ matF HJ)|].
all: split; [intros a Ha Hnf; rewrite KWIN; [exact (HWK a Ha Hnf) | lia | intros Ho; apply Hnf; apply HFPo; exact Ho]|].
all: split; [exact HP|].
all: apply (HQ _ _ _ k1).
all: first
  [ exact (ajournal_x_materializeR (SK := SK) SEGS B (@prh_pst prh_img_B) ARx LAWS (@pa_segs_low _ _ PA)
      (wle' SEGS RZ) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ matF HJ)
  | exact HPM | exact KLOW
  | (intros i Hi; rewrite KC3 by (subst X; lia); rewrite KB2 by lia; rewrite (Hcopy i Hi); apply KA; lia)
  | exact WX | exact W0' | exact W8' | exact W16' | exact W24' ].
Qed.
End h.
End W.
