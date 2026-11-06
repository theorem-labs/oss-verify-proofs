(** One property of an object that is not a Struct (shape <> 7), its first part: 0x1333c -> 0x13450 (UBSan image
    of reac-pw/fuzz_rate's LLVMFuzzerTestOneInput). sel = fuzz_u8 (fuzz.h:39-43; the UBSan check on in->p + 1 at
    0x13348 not taken), the shape test (pod.h:401: the cell sp + 0xb0 against the literal 7, 0x13364-0x1336c), then
    the property's key (SPA_PROP_volume, cell sp + 0x58, when sel & 3 = 0, else SPA_PROP_params, cell sp + 0x78;
    pod.h:407) and flags 0 (pod.h:408) put into buf by two inlined pod_put32 (0x133bc-0x1344c: the capacity tests of
    pod.h:177 false, the UBSan checks of pod.h:179 not taken). The form is reac-pw/fuzz_role's
    U/Prog/RoleBuild/Key.v, re-walked at rate's registers, frame cells and addresses. *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Lib Require Import Tac.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.U Require Import Img0.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.U.Prog Require Import SlotInv LLVMFuzzerTestOneInput_c.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.U.Prog.RateBuild Require Import Facts Cut UTac Kit.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Pod Require Import Cursor Model Layout.
Import ListNotations.
Open Scope Z_scope.

Section Key.
Variables (sp gp tp : word) (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte).
Variables (rest : list byte) (fl src pp lo : Z) (H : hdr).
Hypothesis HOK : BOK sp rest src pp lo.

(** pod_put's capacity test (pod.h:177) at a length below 16381: false. *)
Local Ltac cap_dead :=
  lazymatch goal with
  | |- evt _ _ (MS _ _ (if bv_ltu (Z_to_bv 64 ?x) (Z_to_bv 64 (-16385)) then _ else _) _ _ _ _) =>
      rewrite (cap_lit x) by lia; cbv iota
  end.
(** A UBSan check whose taken side is the good one. *)
Local Ltac refute T := exfalso; zify_cond T; rewrite ?lnot_mod, ?pred_opp_mod in T by lia; lia.
Local Ltac tk T := if_cases T; [ | refute T ].

(** 0x133bc: the key's put32 (a3 = the key) and the flags' put32, to 0x13450. *)
Lemma key_put : forall sh np ps r sel (ra t0 t2 a2 a4 a5 a6 s9 s10 t3 t4 t5 t6 : word) m1,
  sh <> 7 -> 0 <= sel < 256 -> suffix rest r -> pc_wf sh ps -> 0 <= np < 4 -> (length ps < Z.to_nat np)%nat ->
  MBr sp m rest src pp lo (pc_image (PbCut sh ps None)) m1 -> CFIX sp pp m1 -> CPROP sp fl H sh np m1 ->
  evt rsegs (PKEY sp gp tp F fc m rest fl src pp lo H sh np ps r sel)
    (MS (mkR ra sp gp tp t0 (Z_to_bv 64 (Z.of_nat (length r))) t2
             (Z_to_bv 64 (bv_unsigned sp + T_OFF)) (Z_to_bv 64 4)
             (Z_to_bv 64 sel) (Z_to_bv 64 (Z.land sel 3)) a2 (Z_to_bv 64 (key_of sel)) a4 a5 a6
             (Z_to_bv 64 (Z.of_nat (length ps)))
             (Z_to_bv 64 S2V) (Z_to_bv 64 (Z.b2z (seen_of ps))) (Z_to_bv 64 MULT10) (Z_to_bv 64 10)
             (Z_to_bv 64 (Z.lnot pp)) (Z_to_bv 64 (cur rest src r)) (Z_to_bv 64 pp) s9 s10
             (Z_to_bv 64 (pp + POD_LEN_OFF)) t3 t4 t5 t6)
        F (Z_to_bv 64 0x133bc) fc None m1 (seg_rom rsegs)).
Proof.
  intros sh np ps r sel ra t0 t2 a2 a4 a5 a6 s9 s10 t3 t4 t5 t6 m1 Hsh Hsel Hsuf Hwf Hnp Hlt MB CF CP.
  pose proof HOK as (HS0 & HS1 & HP1 & HDJ & HM1 & HL0 & HSP & HPP & HROM & HSROM).
  pose proof CF as (C00 & C50 & C58 & C78 & C80 & C88 & C90 & C98 & CA0 & CB8 & CC0 & CC8 & CD8).
  pose proof CP as (C38 & CA8 & CB0 & CH).
  pose proof CH as (H08 & H10 & H18 & H20 & H28 & H30).
  pose proof Hwf as (Hsh8 & Hv & He & Hl3).
  clear CF CP CH. unfold cell8 in *.
  unfold pc_image in MB. cbn [pc_shape pc_props] in MB.
  pose proof (MBr_bounds _ _ _ _ _ _ _ _ MB) as (PB0 & PB1 & PBL).
  destruct (pc_buf_cap sh ps Hwf ltac:(lia)) as [HL8 HD8].
  assert (LC : bytes_at rsegs m1 (pp + POD_LEN_OFF) (le8 (Z_to_bv 64 (Z.of_nat (length (pc_buf (PbCut sh ps None))))))).
  { pose proof (MBr_pp_bytes _ _ _ _ _ _ _ _ POD_LEN_OFF 8 MB ltac:(unfold POD_LEN_OFF; lia)
                  ltac:(unfold POD_LEN_OFF, POD_PROPS in *; lia)) as X.
    unfold POD_LEN_OFF in X |- *. change (Z.to_nat 16384) with (Z.to_nat OFF_LEN) in X.
    rewrite pp_image_slice_len in X by (unfold POD_BUF_MAX; lia). rewrite le8_lit64. exact X. }
  set (L := Z.of_nat (length (pc_buf (PbCut sh ps None)))) in *.
  assert (HL0' : 0 <= L) by (unfold L; lia).
  unfold POD_PROPS, FRAME_LOCALS, MID_STACK in HP1, PB1, HSP, HM1, HDJ, HS1, PBL.
  (* 0x133bc ld a5,0(s11); ld a2,0xc0(sp); add a2,a5,a2; ld a4,0xb8(sp); 0x133cc bltu a2,a4 (the capacity test) *)
  rd LC. zstep. clear R. rd CC0. zstep. clear R. zstep. rd CB8. zstep. clear R.
  zstep. cap_dead.
  (* 0x133d0 lui; addiw a2 = 0x4001; 0x133d8 bltu a5,a2 (else trap); 0x133e0 bgeu s6,a5 (else trap) *)
  zstep. zstep. zstep. tk T1. zstep. tk T2.
  (* 0x133e8 add a4,s8,a5; srli a5; srli a6; sb a3,0(a4) .. sb zero,3(a4) *)
  zstep. zstep. zstep.
  ppst HOK L 1%nat. clear ST. ppst HOK (L + 1) 1%nat. clear ST. ppst HOK (L + 2) 1%nat. clear ST.
  ppst HOK (L + 3) 1%nat. clear ST.
  (* 0x13404 ld a3,0(s11); addi a5,a3,4; ld a3,0xc0(sp); add a3,a5,a3; sd a5,0(s11) *)
  rd LC. zstep. clear R. zstep. rd CC0. zstep. clear R. zstep.
  ppst HOK POD_LEN_OFF 8%nat. clear LC. rename ST into LC.
  (* the image: the key's put *)
  rewrite (img_put32 _ _ _ _ _ _ L _ _ _ _ (key_of sel)) in MB;
    [ | reflexivity | unfold POD_BUF_MAX; lia | apply key_bytes | apply length_le1 | apply length_le1
      | apply length_le1 | apply length_le1 ].
  (* 0x13418 ld a4,0xb8(sp); 0x1341c bltu (capacity); 0x13420 bltu a5,a2 (else trap); 0x13428 bgeu s6,a5 *)
  rd CB8. zstep. clear R. zstep. cap_dead. zstep. tk T3. zstep. tk T4.
  (* 0x13430 add a2,s8,a5; four zero bytes; 0x13444 ld a2,0(s11); addi a5,a2,4; sd a5,0(s11) *)
  zstep.
  ppst HOK (L + 4) 1%nat. clear ST. ppst HOK (L + 5) 1%nat. clear ST. ppst HOK (L + 6) 1%nat. clear ST.
  ppst HOK (L + 7) 1%nat. clear ST.
  rd LC. zstep. clear R. zstep.
  ppst HOK POD_LEN_OFF 8%nat.
  (* the image: the flags' put *)
  replace (L + 5) with (L + 4 + 1) in MB by lia. replace (L + 6) with (L + 4 + 2) in MB by lia.
  replace (L + 7) with (L + 4 + 3) in MB by lia. replace (L + 8) with (L + 4 + 4) in MB by lia.
  rewrite (img_put32 _ _ _ _ _ _ (L + 4) _ _ _ _ 0) in MB;
    [ | unfold L; rewrite length_app, length_le32; lia | unfold POD_BUF_MAX; lia | vm_compute; reflexivity
      | apply length_le1 | apply length_le1 | apply length_le1 | apply length_le1 ].
  rewrite <- app_assoc in MB.
  apply evt_done. unfold PKEY, PROP_KEY.
  do 16 eexists. eexists. split; [reflexivity|].
  split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
  split; [exact MB|].
  split; [exact (conj C00 (conj C50 (conj C58 (conj C78 (conj C80 (conj C88 (conj C90 (conj C98 (conj CA0
                 (conj CB8 (conj CC0 (conj CC8 CD8))))))))))))|].
  split; [exact (conj C38 (conj CA8 (conj CB0 (conj H08 (conj H10 (conj H18 (conj H20 (conj H28 H30))))))))|].
  repeat (split; [assumption|]). assumption.
Qed.

(** 0x13364, sel read: the shape test against 7, the key's cell, the two puts. *)
Lemma key_from_sel : forall sh np ps r sel (ra t0 t2 a1 a2 a3 a4 a5 a6 s9 s10 t3 t4 t5 t6 : word) m1,
  sh <> 7 -> 0 <= sel < 256 -> suffix rest r -> pc_wf sh ps -> 0 <= np < 4 -> (length ps < Z.to_nat np)%nat ->
  MBr sp m rest src pp lo (pc_image (PbCut sh ps None)) m1 -> CFIX sp pp m1 -> CPROP sp fl H sh np m1 ->
  evt rsegs (PKEY sp gp tp F fc m rest fl src pp lo H sh np ps r sel)
    (MS (mkR ra sp gp tp t0 (Z_to_bv 64 (Z.of_nat (length r))) t2
             (Z_to_bv 64 (bv_unsigned sp + T_OFF)) (Z_to_bv 64 4)
             (Z_to_bv 64 sel) a1 a2 a3 a4 a5 a6 (Z_to_bv 64 (Z.of_nat (length ps)))
             (Z_to_bv 64 S2V) (Z_to_bv 64 (Z.b2z (seen_of ps))) (Z_to_bv 64 MULT10) (Z_to_bv 64 10)
             (Z_to_bv 64 (Z.lnot pp)) (Z_to_bv 64 (cur rest src r)) (Z_to_bv 64 pp) s9 s10
             (Z_to_bv 64 (pp + POD_LEN_OFF)) t3 t4 t5 t6)
        F (Z_to_bv 64 0x13364) fc None m1 (seg_rom rsegs)).
Proof.
  intros sh np ps r sel ra t0 t2 a1 a2 a3 a4 a5 a6 s9 s10 t3 t4 t5 t6 m1 Hsh Hsel Hsuf Hwf Hnp Hlt MB CF CP.
  pose proof CF as (C00 & C50 & C58 & C78 & C80 & C88 & C90 & C98 & CA0 & CB8 & CC0 & CC8 & CD8).
  pose proof CP as (C38 & CA8 & CB0 & CH).
  pose proof Hwf as (Hsh8 & Hv & He & Hl3).
  unfold cell8 in CB0, C78, C58.
  (* 0x13364 ld a1,0xb0(sp); 0x13368 addi a2,zero,7; 0x1336c bne a1,a2 *)
  rd CB0. zstep. clear R. zstep. zstep. if_cases E7; zify_cond E7; [|exfalso; lia].
  (* 0x133ac andi a1,a0,3; 0x133b0 ld a3,0x78(sp); 0x133b4 bnez a1 *)
  zstep. rd C78. zstep. clear R. zstep. if_cases E1; zify_cond E1.
  - assert (Ek : key_of sel = POD_PROP_PARAMS).
    { unfold key_of. rewrite land3 in E1. replace (sel mod 4 =? 0) with false; [reflexivity|].
      symmetry. apply Z.eqb_neq. lia. }
    rewrite <- Ek. eapply key_put; eassumption.
  - (* 0x133b8 ld a3,0x58(sp) *)
    rd C58. zstep. clear R.
    assert (Ek : key_of sel = POD_PROP_VOLUME).
    { unfold key_of. rewrite land3 in E1. replace (sel mod 4 =? 0) with true; [reflexivity|].
      symmetry. apply Z.eqb_eq. lia. }
    rewrite <- Ek. eapply key_put; eassumption.
Qed.

(** 0x1333c -> 0x13450: sel = fuzz_u8, then [key_from_sel]. *)
Lemma key_entry : forall sh np ps r ms,
  PROPH sp gp tp F fc m rest fl src pp lo H sh np ps r ms -> sh <> 7 ->
  evt rsegs (PKEY sp gp tp F fc m rest fl src pp lo H sh np ps (snd (fuzz_u8 r)) (fst (fuzz_u8 r))) ms.
Proof.
  intros sh np ps r ms
    (ra & t0 & t2 & a0 & a1 & a2 & a3 & a4 & a5 & a6 & s9 & s10 & t3 & t4 & t5 & t6 & m1 & -> &
     MB & CF & CP & Hsuf & Hwf & Hnp & Hlt) Hsh.
  pose proof HOK as (HS0 & HS1 & HP1 & HDJ & HM1 & HL0 & HSP & HPP & HROM & HSROM).
  pose proof Hsuf as [j [Hj Er]].
  assert (Hcur : cur rest src r = src + Z.of_nat j) by (unfold cur; rewrite Er, length_skipn; lia).
  assert (Hrl : Z.of_nat (length r) = Z.of_nat (length rest) - Z.of_nat j) by (rewrite Er, length_skipn; lia).
  pose proof (bv_unsigned_in_range 64 sp) as SPR. change (bv_modulus 64) with 18446744073709551616 in SPR.
  unfold MID_STACK, FRAME_LOCALS in HM1, HSP.
  unfold PROP_HEAD.
  (* 0x1333c beqz t1 *)
  zstep. if_cases E0; zify_cond E0.
  - destruct r as [|b r1]; [|cbn [length] in E0, Hrl; lia].
    (* 0x13360 mv a0,zero *)
    zstep. cbn [fuzz_u8 fst snd].
    eapply key_from_sel; try eassumption; lia.
  - destruct r as [|b r1]; [cbn [length] in E0, Hrl; lia|].
    assert (HB : ov_read_bytes rsegs m1 (wa (src + Z.of_nat j)) 1 = Some [b])
      by (eapply MBr_byte; [exact MB | symmetry; exact Er]).
    (* 0x13340 addi a1,s7,1; addi a0,zero,1; 0x13348 bltu a0,a1 (else trap) *)
    zstep. zstep. zstep. tk T0.
    (* 0x13350 lbu a0,0(s7); addi t1,t1,-1; mv s7,a1; j 0x13364 *)
    zstep. zstep. zstep. zstep.
    cbn [fuzz_u8 fst snd].
    replace (Z.of_nat (length (b :: r1)) + -1) with (Z.of_nat (length r1)) by (cbn [length]; lia).
    replace (cur rest src (b :: r1) + 1) with (cur rest src r1) by (unfold cur; cbn [length]; lia).
    eapply key_from_sel; try eassumption.
    + pose proof (bv_unsigned_in_range 8 b). change (bv_modulus 8) with 256 in *. lia.
    + exists (S j). split.
      * destruct (Nat.le_gt_cases (S j) (length rest)) as [Hle|Hgt]; [exact Hle|].
        exfalso. rewrite skipn_all2 in Er by lia. discriminate.
      * rewrite <- (skipn_skipn 1 j). rewrite <- Er. reflexivity.
Qed.

End Key.
