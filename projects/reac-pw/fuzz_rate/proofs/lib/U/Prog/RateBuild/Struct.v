(** One property, a params Struct (sel & 3 <> 0, sel bit 4 clear): 0x13450 -> the pod loop's head 0x13560, or
    the Struct's close 0x14080 when no byte is left (0x13508) or the count is 0 (0x13550 -> 0x14030). `first`
    into its cell (pod.h:409-411), the Struct's placeholder size word and its type put into buf (pod.h:420-423, the
    UBSan checks of pod.h:179 and the capacity tests false), the count = fuzz_u8 % 33 by the multiply with the
    .rodata magic at 0x10550 (pod.h:424; the UBSan check on cursor + 1 not taken), and the loop's cells (at,
    seen_params, i, count, &buf[at]). The walk of reac-pw/fuzz_role's U/Prog/RoleBuild/Struct.v, re-walked at
    rate's registers, frame cells and addresses. *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Lib Require Import Tac.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.U Require Import Img0.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.U.Prog Require Import SlotInv LLVMFuzzerTestOneInput_c.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.U.Prog.RateBuild Require Import Facts Cut UTac Kit.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Pod Require Import Cursor Model Layout.
Import ListNotations.
Open Scope Z_scope.

(** An open Struct with no pod yet records the same pods as no open Struct. *)
Lemma pc_ents_open0 : forall sh ps, pc_ents (PbCut sh ps (Some [])) = pc_ents (PbCut sh ps None).
Proof. intros sh ps. unfold pc_ents. cbn [pc_props pc_open]. destruct (first_params ps) as [[]|]; reflexivity. Qed.

(** The block after the placeholder size word and the type: the cut with an open, empty Struct. *)
Lemma open_img : forall sh ps sel, key_of sel = POD_PROP_PARAMS ->
  pp_image (((pc_buf (PbCut sh ps None) ++ le32 (key_of sel) ++ le32 0) ++ le32 0) ++ le32 14)
    (is_props (PodRec sh ps None)) (has_params (PodRec sh ps None)) (params_struct (PodRec sh ps None))
    (pc_ents (PbCut sh ps None)) false
  = pc_image (PbCut sh ps (Some [])).
Proof.
  intros sh ps sel Ek. unfold pc_image. cbn [pc_shape pc_props]. rewrite pc_ents_open0, <- pc_buf_open, Ek.
  rewrite <- !app_assoc. reflexivity.
Qed.

Lemma land16 : forall z, Z.testbit z 4 = false -> Z.land z 16 = 0.
Proof.
  intros z H. apply Z.bits_inj'. intros n Hn. rewrite Z.land_spec, Z.bits_0. change 16 with (2^4).
  rewrite Z.pow2_bits_eqb by lia. destruct (Z.eqb_spec 4 n); [subst; rewrite H; reflexivity | apply andb_false_r].
Qed.

(** count = u8 % 33 as the code computes it (pod.h:424): the high half of u8 * 0x07c1f07c1f07c1f1 (the .rodata
    word at 0x10550) is u8 / 33, times 33 by a shift and an or (the quotient is below 8). *)
Lemma mod33_magic : forall x, 0 <= x < 256 ->
  x - Z.lor (Z.shiftl (Z.shiftr (x * 558992244657865201) 64 mod 18446744073709551616) 5 mod 18446744073709551616)
            (Z.shiftr (x * 558992244657865201) 64 mod 18446744073709551616)
  = x mod 33.
Proof.
  intros x Hx.
  assert (H : forallb (fun y => Z.eqb (y - Z.lor (Z.shiftl (Z.shiftr (y * 558992244657865201) 64
                                                               mod 18446744073709551616) 5 mod 18446744073709551616)
                                               (Z.shiftr (y * 558992244657865201) 64 mod 18446744073709551616))
                                      (y mod 33))
                      (map Z.of_nat (seq 0 256)) = true) by (vm_compute; reflexivity).
  rewrite forallb_forall in H. apply Z.eqb_eq, H. apply in_map_iff. exists (Z.to_nat x). split; [lia|].
  apply in_seq. lia.
Qed.

Section Struct.
Variables (sp gp tp : word) (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte).
Variables (rest : list byte) (fl src pp lo : Z) (H : hdr).
Hypothesis HOK : BOK sp rest src pp lo.

Local Ltac cap_dead :=
  lazymatch goal with
  | |- evt _ _ (MS _ _ (if bv_ltu (Z_to_bv 64 ?x) (Z_to_bv 64 (-16385)) then _ else _) _ _ _ _) =>
      rewrite (cap_lit x) by lia; cbv iota
  end.
Local Ltac refute T := exfalso; zify_cond T; rewrite ?lnot_mod, ?pred_opp_mod in T by lia; lia.
Local Ltac tk T := if_cases T; [ | refute T ].

(** The target: the pod loop's head with no pod yet, or the close when the count is 0 or no byte is left. *)
Definition SOPEN (sh np : Z) (ps : list (Z * pval)) (r : list byte) : machine_state -> Prop :=
  fun ms =>
    (0 < fst (fuzz_u8 r) mod 33 /\
     CNTH sp gp tp F fc m rest fl src pp lo H sh np ps (length ps) (fst (fuzz_u8 r) mod 33) [] 0 (snd (fuzz_u8 r)) ms) \/
    (fst (fuzz_u8 r) mod 33 = 0 /\
     PCLOSE sp gp tp F fc m rest fl src pp lo H sh np ps (length ps) [] (snd (fuzz_u8 r)) ms).

Lemma struct_open : forall sh np ps r sel ms,
  PKEY sp gp tp F fc m rest fl src pp lo H sh np ps r sel ms -> sel mod 4 <> 0 -> Z.testbit sel 4 = false ->
  evt rsegs (SOPEN sh np ps r) ms.
Proof.
  intros sh np ps r sel ms
    (ra & t0 & t2 & a0 & a1 & a2 & a3 & a4 & a5 & a6 & s9 & s10 & t3 & t4 & t5 & t6 & m1 & -> &
     -> & -> & -> & MB & CF & CP & Hsuf & Hwf & Hnp & Hlt & Hsh & Hsel) H4 Hb4.
  pose proof HOK as (HS0 & HS1 & HP1 & HDJ & HM1 & HL0 & HSP & HPP & HROM & HSROM).
  pose proof CF as (C00 & C50 & C58 & C78 & C80 & C88 & C90 & C98 & CA0 & CB8 & CC0 & CC8 & CD8).
  unfold CPROP, CHDR in CP.
  pose proof CP as (C38 & CA8 & CB0 & H08 & H10 & H18 & H20 & H28 & H30).
  pose proof Hwf as (Hsh8 & Hv & He & Hl3).
  clear CF CP. unfold cell8 in *.
  assert (Ek : key_of sel = POD_PROP_PARAMS)
    by (unfold key_of; replace (sel mod 4 =? 0) with false; [reflexivity | symmetry; apply Z.eqb_neq; exact H4]).
  assert (Hl4 : Z.land sel 3 <> 0) by (rewrite land3; exact H4).
  unfold kimg in MB.
  pose proof (MBr_bounds _ _ _ _ _ _ _ _ MB) as (PB0 & PB1 & PBL).
  destruct (pc_buf_cap sh ps Hwf ltac:(lia)) as [HL8 HD8].
  assert (LC : bytes_at rsegs m1 (pp + POD_LEN_OFF)
                 (le8 (Z_to_bv 64 (Z.of_nat (length (pc_buf (PbCut sh ps None) ++ le32 (key_of sel) ++ le32 0)))))).
  { pose proof (MBr_pp_bytes _ _ _ _ _ _ _ _ POD_LEN_OFF 8 MB ltac:(unfold POD_LEN_OFF; lia)
                  ltac:(unfold POD_LEN_OFF, POD_PROPS in *; lia)) as X.
    unfold POD_LEN_OFF in X |- *. change (Z.to_nat 16384) with (Z.to_nat OFF_LEN) in X.
    rewrite pp_image_slice_len in X by (rewrite !length_app, !length_le32; unfold POD_BUF_MAX; lia).
    rewrite le8_lit64. exact X. }
  replace (Z.of_nat (length (pc_buf (PbCut sh ps None) ++ le32 (key_of sel) ++ le32 0)))
    with (Z.of_nat (length (pc_buf (PbCut sh ps None))) + 8) in LC by (rewrite !length_app, !length_le32; lia).
  set (L := Z.of_nat (length (pc_buf (PbCut sh ps None)))) in *.
  assert (HL0' : 0 <= L) by (unfold L; lia).
  unfold POD_PROPS, FRAME_LOCALS, MID_STACK in HP1, PB1, HSP, HM1, HDJ, HS1, PBL.
  (* the pc as a literal, so the auipc-relative load of the .rodata magic (0x10550) has a literal address *)
  unfold PROP_KEY.
  (* 0x13450 mv s9,s3; beqz a1 (not taken: a1 = sel & 3 <> 0); addi s9,zero,1 *)
  zstep. zstep. if_cases E1; zify_cond E1; [exfalso; lia|]. zstep.
  (* 0x1345c snez a2,a1; seqz a3,s3; and a2,a2,a3; sd a2,0xe0(sp) (first) *)
  zstep. zstep. zstep. stst HOK 0xe0 8%nat. rename ST into CE0.
  (* 0x1346c beqz a1 (not taken); andi a0,a0,0x10; bnez a0 (not taken: bit 4 clear) *)
  zstep. if_cases E2; zify_cond E2; [exfalso; lia|].
  zstep. zstep. if_cases E3; zify_cond E3; [exfalso; exact (E3 (land16 sel Hb4))|].
  assert (Ef : Z.land (Z.b2z (0 <? Z.land sel 3)) (Z.b2z (Z.b2z (seen_of ps) <? 1)) = Z.b2z (first_of ps)).
  { replace (0 <? Z.land sel 3) with true
      by (symmetry; apply Z.ltb_lt; rewrite land3; pose proof (Z.mod_pos_bound sel 4); lia).
    unfold first_of. destruct (seen_of ps); reflexivity. }
  rewrite Ef in CE0. clear Ef.
  (* 0x13478 the placeholder size word: ld a1,0xc0(sp); add a1,a5,a1; add a4,s8,a5; mv a0,a5; ld a2,0xb8(sp);
     0x1348c bltu a1,a2 (capacity, false) *)
  rd CC0. zstep. clear R. zstep. zstep. zstep. rd CB8. zstep. clear R. zstep. cap_dead.
  (* 0x13490 lui; addiw a1 = 0x4001; 0x13498 bltu a5,a1 (else trap); 0x134a0 bgeu s6,a5 (else trap) *)
  zstep. zstep. zstep. tk T1. zstep. tk T2.
  (* 0x134a8 sb zero,0(a4) .. sb zero,3(a4) *)
  ppst HOK (L + 8) 1%nat. clear ST. ppst HOK (L + 9) 1%nat. clear ST. ppst HOK (L + 10) 1%nat. clear ST.
  ppst HOK (L + 11) 1%nat. clear ST.
  (* 0x134b8 ld a0,0(s11); addi a0,a0,4; ld a2,0xc0(sp); add a2,a0,a2; sd a0,0(s11) *)
  rd LC. zstep. clear R. zstep. rd CC0. zstep. clear R. zstep.
  ppst HOK POD_LEN_OFF 8%nat. clear LC. rename ST into LC.
  replace (L + 9) with (L + 8 + 1) in MB by lia. replace (L + 10) with (L + 8 + 2) in MB by lia.
  replace (L + 11) with (L + 8 + 3) in MB by lia. replace (L + 12) with (L + 8 + 4) in MB by lia.
  rewrite (img_put32 _ _ _ _ _ _ (L + 8) _ _ _ _ 0) in MB;
    [ | unfold L; rewrite !length_app, !length_le32; lia | unfold POD_BUF_MAX; lia | vm_compute; reflexivity
      | apply length_le1 | apply length_le1 | apply length_le1 | apply length_le1 ].
  (* 0x134cc ld a3,0xb8(sp); 0x134d0 bltu a2,a3 (capacity, false); 0x134d4 bltu a0,a1 (else trap);
     0x134dc bgeu s6,a0 (else trap) *)
  rd CB8. zstep. clear R. zstep. cap_dead. zstep. tk T3. zstep. tk T4.
  (* 0x134e4 add a0,s8,a0; addi a1,zero,0xe; sb a1,0(a0); sb zero,1..3(a0); ld a0,0(s11); addi a0,a0,4;
     sd a0,0(s11) *)
  zstep. zstep.
  ppst HOK (L + 12) 1%nat. clear ST. ppst HOK (L + 13) 1%nat. clear ST. ppst HOK (L + 14) 1%nat. clear ST.
  ppst HOK (L + 15) 1%nat. clear ST.
  rd LC. zstep. clear R. zstep.
  ppst HOK POD_LEN_OFF 8%nat. clear LC. rename ST into LC.
  replace (L + 13) with (L + 12 + 1) in MB by lia. replace (L + 14) with (L + 12 + 2) in MB by lia.
  replace (L + 15) with (L + 12 + 3) in MB by lia. replace (L + 16) with (L + 12 + 4) in MB by lia.
  rewrite (img_put32 _ _ _ _ _ _ (L + 12) _ _ _ _ 14) in MB;
    [ | unfold L; rewrite !length_app, !length_le32; lia | unfold POD_BUF_MAX; lia | vm_compute; reflexivity
      | apply length_le1 | apply length_le1 | apply length_le1 | apply length_le1 ].
  rewrite (open_img sh ps sel Ek) in MB.
  assert (Lo : Z.of_nat (length (pc_buf (PbCut sh ps (Some [])))) = L + 16)
    by (unfold L; rewrite <- pc_buf_open, !length_app, !length_le32; lia).
  pose proof Hsuf as [j [Hj Er]].
  assert (Hcur : cur rest src r = src + Z.of_nat j) by (unfold cur; rewrite Er, length_skipn; lia).
  assert (Hrl : Z.of_nat (length r) = Z.of_nat (length rest) - Z.of_nat j) by (rewrite Er, length_skipn; lia).
  pose proof (bv_unsigned_in_range 64 sp) as SPR. change (bv_modulus 64) with 18446744073709551616 in SPR.
  (* 0x13508 beqz t1: no input left, count 0, straight to the close 0x14080 *)
  zstep. if_cases E4; zify_cond E4.
  - destruct r as [|b r1]; [|cbn [length] in E4, Hrl; lia].
    apply evt_done. right. cbn [fuzz_u8 fst snd]. split; [reflexivity|].
    rewrite <- Lo.
    do 13 eexists. eexists. split; [reflexivity|].
    split; [exact MB|].
    split; [exact (conj C00 (conj C50 (conj C58 (conj C78 (conj C80 (conj C88 (conj C90 (conj C98 (conj CA0
                   (conj CB8 (conj CC0 (conj CC8 CD8))))))))))))|].
    split; [exact (conj C38 (conj CA8 (conj CB0 (conj H08 (conj H10 (conj H18 (conj H20 (conj H28 H30))))))))|].
    split; [exact CE0|].
    split; [|cbn [length]; lia].
    split; [exact Hsuf|]. split; [exact Hwf|]. split; [exact Hsh|]. split; [exact Hnp|].
    split; [reflexivity|]. split; [exact Hlt | constructor].
  - destruct r as [|b r1]; [cbn [length] in E4, Hrl; lia|].
    (* 0x1350c the loop's cells at, seen_params, i *)
    stst HOK 0x60 8%nat. rename ST into C60. stst HOK 0x68 8%nat. rename ST into C68.
    stst HOK 0x70 8%nat. rename ST into C70.
    (* 0x13518 addi s9,s7,1; addi a1,zero,1; bltu a1,s9 (else trap) *)
    zstep. zstep. zstep. tk T5.
    lazymatch goal with
    | |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
        assert (HB : ov_read_bytes rsegs mm (wa (src + Z.of_nat j)) 1 = Some [b])
          by (eapply MBr_byte; [exact MB | symmetry; exact Er])
    end.
    pose proof MB as (_ & _ & _ & _ & _ & _ & MIx & _).
    (* 0x13528 lbu a1,0(s7); auipc; ld a2 (the magic); mulhu; slli; or; sub; addi t1,t1,-1 *)
    zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep.
    pose proof (bv_unsigned_in_range 8 b) as BR. change (bv_modulus 8) with 256 in BR.
    rewrite (mod33_magic (bv_unsigned b) BR).
    replace (Z.of_nat (length (b :: r1)) + -1) with (Z.of_nat (length r1)) by (cbn [length]; lia).
    replace (cur rest src (b :: r1) + 1) with (cur rest src r1) by (unfold cur; cbn [length]; lia).
    assert (Hsuf1 : suffix rest r1).
    { exists (S j). split.
      - destruct (Nat.le_gt_cases (S j) (length rest)) as [Hle|Hle]; [exact Hle|].
        exfalso. rewrite skipn_all2 in Er by lia. discriminate.
      - rewrite <- (skipn_skipn 1 j). rewrite <- Er. reflexivity. }
    (* 0x13548 sd a1,0xd0(sp) (count); lui s6,4; 0x13550 beqz a1 *)
    stst HOK 0xd0 8%nat. rename ST into CD0.
    pose proof (Z.mod_pos_bound (bv_unsigned b) 33 ltac:(lia)) as Hc.
    zstep. zstep. if_cases E5; zify_cond E5.
    + (* count 0: 0x14030 mv s7,s9; ld s6,0x50(sp); ld a7,0x70(sp); ld s9,0x68(sp); ld a5,0x60(sp);
         j 0x14080 *)
      zstep. rd C50. zstep. clear R. rd C70. zstep. clear R. rd C68. zstep. clear R. rd C60. zstep. clear R.
      zstep.
      apply evt_done. right. cbn [fuzz_u8 fst snd]. split; [lia|].
      rewrite <- Lo.
      do 13 eexists. eexists. split; [reflexivity|].
      split; [exact MB|].
      split; [exact (conj C00 (conj C50 (conj C58 (conj C78 (conj C80 (conj C88 (conj C90 (conj C98 (conj CA0
                     (conj CB8 (conj CC0 (conj CC8 CD8))))))))))))|].
      split; [exact (conj C38 (conj CA8 (conj CB0 (conj H08 (conj H10 (conj H18 (conj H20 (conj H28 H30))))))))|].
      split; [exact CE0|].
      split; [|cbn [length]; lia].
      split; [exact Hsuf1|]. split; [exact Hwf|]. split; [exact Hsh|]. split; [exact Hnp|].
      split; [reflexivity|]. split; [exact Hlt | constructor].
    + (* 0x13554 sd a4,0x40(sp); mv s10,t1; mv s3,zero: the pod loop's head 0x13560 *)
      stst HOK 0x40 8%nat. rename ST into C40.
      zstep. zstep.
      apply evt_done. left. cbn [fuzz_u8 fst snd]. split; [lia|].
      do 19 eexists. eexists. split; [reflexivity|].
      split; [exact MB|].
      split; [exact (conj C00 (conj C50 (conj C58 (conj C78 (conj C80 (conj C88 (conj C90 (conj C98 (conj CA0
                     (conj CB8 (conj CC0 (conj CC8 CD8))))))))))))|].
      split; [exact (conj (conj C38 (conj CA8 (conj CB0 (conj H08 (conj H10 (conj H18 (conj H20 (conj H28 H30))))))))
                          (conj C40 (conj C60 (conj C68 (conj C70 (conj CD0 CE0))))))|].
      split; [|split; [reflexivity | lia]].
      split; [exact Hsuf1|]. split; [exact Hwf|]. split; [exact Hsh|]. split; [exact Hnp|].
      split; [reflexivity|]. split; [exact Hlt | constructor].
Qed.

End Struct.
