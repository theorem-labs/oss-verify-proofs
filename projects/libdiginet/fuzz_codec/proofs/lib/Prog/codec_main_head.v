From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Lib Require Import PropExec MState Mem Cells Exec Step Frame Tac Bytes.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib Require Import Img0.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Spec Require Import DgnSpec DgnLib.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Prog Require Import codec_owe codec_cells codec_img codec_main_inv
  memset_c diginet_personality_of_c LLVMFuzzerTestOneInput_c.
Import ListNotations.
Open Scope Z_scope.

Ltac addr_eq_tac ::= first [ apply wa_of_var; lia
                           | symmetry; first [ apply wa_of_Z_to_bv; lia | apply wa_of_var; lia | unfold wa; f_equal; lia ] ].

(** ---- frame pieces ---- *)

(** Two cell lists with the same bytes and size describe the same memory. *)
Lemma rw_cells_conv : forall m A cs cs',
  rw_cells rsegs m A cs -> cells_wf cs' -> cells_bytes cs' = cells_bytes cs -> cells_size cs' = cells_size cs ->
  rw_cells rsegs m A cs'.
Proof.
  intros m A cs cs' [[W B] Hw] W' Eb Es.
  split; [split; [exact W' | rewrite Eb; exact B] | rewrite Es; exact Hw].
Qed.

(** The HEAD frame cut in three: the constants, k (184 bytes, memset first), and in.p, in.n, the tail. *)
Lemma head_split : forall e m1 c kj rj,
  rw_cells rsegs m1 (bv_unsigned (e_sp e) + -400) (head_cells e c kj rj) ->
  rw_cells rsegs m1 (bv_unsigned (e_sp e) + -400) [C8 (Z_to_bv 64 0x5cb0); C8 (Z_to_bv 64 0x13f0)] /\
  rw_cells rsegs m1 (bv_unsigned (e_sp e) + -384) [CB 184 kj] /\
  rw_cells rsegs m1 (bv_unsigned (e_sp e) + -200)
    [C8 (Z_to_bv 64 (bv_unsigned (e_p e) + c)); CB 8 (firstn 8 rj); CB 80 (skipn 8 rj)].
Proof.
  intros e m1 c kj rj H. unfold head_cells in H.
  change [C8 (Z_to_bv 64 0x5cb0); C8 (Z_to_bv 64 0x13f0); CB 184 kj; C8 (Z_to_bv 64 (bv_unsigned (e_p e) + c));
          CB 88 rj]
    with ([C8 (Z_to_bv 64 0x5cb0); C8 (Z_to_bv 64 0x13f0)] ++ [CB 184 kj] ++
          [C8 (Z_to_bv 64 (bv_unsigned (e_p e) + c)); CB 88 rj]) in H.
  destruct (rw_cells_app_split _ _ _ _ H) as [H1 H23].
  destruct (rw_cells_app_split _ _ _ _ H23) as [H2 H3].
  cbn [cells_size csize Nat.add] in H2, H3.
  replace (bv_unsigned (e_sp e) + -400 + Z.of_nat 16) with (bv_unsigned (e_sp e) + -384) in H2, H3 by lia.
  replace (bv_unsigned (e_sp e) + -384 + Z.of_nat 184) with (bv_unsigned (e_sp e) + -200) in H3 by lia.
  split; [exact H1 | split; [exact H2 | ]].
  pose proof (cells_at_wf _ _ _ _ (proj1 H3)) as W. cbn [cells_wf cell_wf] in W. destruct W as (_ & HL & _).
  apply (rw_cells_conv _ _ _ _ H3).
  - cbn [cells_wf cell_wf]. rewrite length_firstn, length_skipn, HL.
    split; [exact I | split; [reflexivity | split; [reflexivity | exact I]]].
  - cbn [cells_bytes cbytes]. rewrite !app_nil_r, firstn_skipn. reflexivity.
  - reflexivity.
Qed.

(** memset's cells with the argument registers literals. *)
Lemma memset_cells : forall m A (v n : Z), 0 <= v < 2 ^ 64 -> 0 <= n < 2 ^ 64 ->
  rw_cells rsegs m A [CB (Z.to_nat (bv_unsigned (Z_to_bv 64 n)))
                        (repeat (Z_to_bv 8 (bv_unsigned (Z_to_bv 64 v) mod 256)) (Z.to_nat (bv_unsigned (Z_to_bv 64 n))))] ->
  rw_cells rsegs m A [CB (Z.to_nat n) (repeat (Z_to_bv 8 (v mod 256)) (Z.to_nat n))].
Proof. intros m A v n Hv Hn H. rewrite !unsigned_lit in H by lia. exact H. Qed.

(** k after memset(k, 0, 0xb8), cut for the stores of kind, p, desk and for memset(before, 0xa5, 0x40). *)
Lemma k0_split : forall m A,
  rw_cells rsegs m A [CB (Z.to_nat 184) (repeat (Z_to_bv 8 (0 mod 256)) (Z.to_nat 184))] ->
  rw_cells rsegs m A
    [CB 4 (fz0 4); CB 4 (fz0 4); CB 8 (fz0 8); CB 8 (fz0 8);
     C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); CB 24 (fz0 24);
     C8 (Z_to_bv 64 0); C4 (Z_to_bv 64 0)] /\
  rw_cells rsegs m (A + 76) [CB 64 (fz0 64)] /\
  rw_cells rsegs m (A + 140)
    [C4 (Z_to_bv 64 0); CB 24 (fz0 24); C8 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0)].
Proof.
  intros m A H.
  assert (H' : rw_cells rsegs m A
    ([CB 4 (fz0 4); CB 4 (fz0 4); CB 8 (fz0 8); CB 8 (fz0 8);
      C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); CB 24 (fz0 24);
      C8 (Z_to_bv 64 0); C4 (Z_to_bv 64 0)] ++ [CB 64 (fz0 64)] ++
     [C4 (Z_to_bv 64 0); CB 24 (fz0 24); C8 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0)])).
  { apply (rw_cells_conv _ _ _ _ H); vm_compute; [repeat split | reflexivity | reflexivity]. }
  destruct (rw_cells_app_split _ _ _ _ H') as [H1 H23].
  destruct (rw_cells_app_split _ _ _ _ H23) as [H2 H3].
  cbn [cells_size csize Nat.add] in H2, H3.
  replace (A + Z.of_nat 76 + Z.of_nat 64) with (A + 140) in H3 by lia.
  split; [exact H1 | split; [exact H2 | exact H3]].
Qed.

(** before and out after memset(before, 0xa5, 0x40). *)
Lemma a5_cells : forall m A,
  rw_cells rsegs m A [CB (Z.to_nat 64) (repeat (Z_to_bv 8 (165 mod 256)) (Z.to_nat 64))] ->
  rw_cells rsegs m A [CB 32 (fa5 32); CB 32 (fa5 32)].
Proof. intros m A H. apply (rw_cells_conv _ _ _ _ H); vm_compute; [repeat split | reflexivity | reflexivity]. Qed.

(** The pieces back in the shape rd_ok takes. *)
Lemma head_join : forall e m kind pv dv c rem tl,
  rw_cells rsegs m (bv_unsigned (e_sp e) + -400) [C8 (Z_to_bv 64 0x5cb0); C8 (Z_to_bv 64 0x13f0)] ->
  rw_cells rsegs m (bv_unsigned (e_sp e) + -384)
    [C4 (Z_to_bv 64 kind); CB 4 (fz0 4); C8 (Z_to_bv 64 pv); C8 (Z_to_bv 64 dv);
     C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); CB 24 (fz0 24);
     C8 (Z_to_bv 64 0); C4 (Z_to_bv 64 0)] ->
  rw_cells rsegs m (bv_unsigned (e_sp e) + -308) [CB 32 (fa5 32); CB 32 (fa5 32)] ->
  rw_cells rsegs m (bv_unsigned (e_sp e) + -244)
    [C4 (Z_to_bv 64 0); CB 24 (fz0 24); C8 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0)] ->
  rw_cells rsegs m (bv_unsigned (e_sp e) + -200)
    [C8 (Z_to_bv 64 (bv_unsigned (e_p e) + c)); C8 (Z_to_bv 64 rem); CB 80 tl] ->
  rw_cells rsegs m (bv_unsigned (e_sp e) + -400) (body_cells e (k_rd kind pv dv) c rem tl).
Proof.
  intros e m kind pv dv c rem tl H1 H2 H3 H4 H5.
  change (body_cells e (k_rd kind pv dv) c rem tl) with
    ([C8 (Z_to_bv 64 0x5cb0); C8 (Z_to_bv 64 0x13f0)] ++
     [C4 (Z_to_bv 64 kind); CB 4 (fz0 4); C8 (Z_to_bv 64 pv); C8 (Z_to_bv 64 dv);
      C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); CB 24 (fz0 24);
      C8 (Z_to_bv 64 0); C4 (Z_to_bv 64 0)] ++
     [CB 32 (fa5 32); CB 32 (fa5 32)] ++
     [C4 (Z_to_bv 64 0); CB 24 (fz0 24); C8 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0)] ++
     [C8 (Z_to_bv 64 (bv_unsigned (e_p e) + c)); C8 (Z_to_bv 64 rem); CB 80 tl]).
  apply rw_cells_app_join; [exact H1|]. cbn [cells_size csize Nat.add].
  replace (bv_unsigned (e_sp e) + -400 + Z.of_nat 16) with (bv_unsigned (e_sp e) + -384) by lia.
  apply rw_cells_app_join; [exact H2|]. cbn [cells_size csize Nat.add].
  replace (bv_unsigned (e_sp e) + -384 + Z.of_nat 76) with (bv_unsigned (e_sp e) + -308) by lia.
  apply rw_cells_app_join; [exact H3|]. cbn [cells_size csize Nat.add].
  replace (bv_unsigned (e_sp e) + -308 + Z.of_nat 64) with (bv_unsigned (e_sp e) + -244) by lia.
  apply rw_cells_app_join; [exact H4|]. cbn [cells_size csize Nat.add].
  replace (bv_unsigned (e_sp e) + -244 + Z.of_nat 44) with (bv_unsigned (e_sp e) + -200) by lia.
  exact H5.
Qed.

(** ---- the arithmetic of 0x132f0-0x13334 ---- *)

Lemma land255_small : forall x, 0 <= x < 256 -> Z.land x 255 = x.
Proof. intros x Hx. change 255 with (Z.ones 8). rewrite Z.land_ones by lia. apply Z.mod_small. exact Hx. Qed.

(** q % 3 as subw / slli / subw / andi compute it from q and q / 3. *)
Lemma mod3_form : forall q, 0 <= q < 18 ->
  Z.land (bv_swrap 32 (bv_swrap 32 (q - q / 3) mod 18446744073709551616 -
                       (q / 3 * 2 ^ 1) mod 18446744073709551616) mod 18446744073709551616) 255 = q mod 3.
Proof.
  intros q H. apply Z.eqb_eq.
  refine (zall_range (fun x => Z.land (bv_swrap 32 (bv_swrap 32 (x - x / 3) mod 18446744073709551616 -
                       (x / 3 * 2 ^ 1) mod 18446744073709551616) mod 18446744073709551616) 255 =? x mod 3)
            0 18 _ q H).
  vm_compute. reflexivity.
Qed.

(** One input byte, as a value the walk does not need to relate to the input. *)
Lemma byte_read_ex : forall m a bs k, bytes_at rsegs m a bs -> 0 <= k < Z.of_nat (length bs) ->
  exists b, ov_read_bytes rsegs m (wa (a + k)) 1 = Some [b].
Proof. intros m a bs k H Hk. eexists. exact (bytes_at_byte m a bs k H Hk). Qed.

(** op % 15 as add / slli / subw / andi compute it from op and op / 15. *)
Lemma kind_form : forall x, 0 <= x < 256 ->
  Z.land (bv_swrap 32 (x + x / 15 - x / 15 * 16) mod 18446744073709551616) 255 = x mod 15.
Proof.
  intros x H. apply Z.eqb_eq.
  refine (zall_range (fun y => Z.land (bv_swrap 32 (y + y / 15 - y / 15 * 16) mod 18446744073709551616) 255
                               =? y mod 15) 0 256 _ x H).
  vm_compute. reflexivity.
Qed.

Lemma pers_of_range : forall i, 0 <= pers_of i < 2 ^ 64.
Proof. intros i. unfold pers_of, PERS. destruct (i =? 1); [lia|]. destruct (i =? 2); lia. Qed.

Lemma spec_desk_range : forall i, 0 <= nth (Z.to_nat i) codec_SPEC_DESK 0 < 2 ^ 64.
Proof.
  intros i. unfold codec_SPEC_DESK.
  destruct (Z.to_nat i) as [|[|[|j]]]; cbn [nth]; [lia | lia | lia | destruct j; lia].
Qed.

(** ---- the desk ---- *)

(** The desk DESK[i] / SPEC_DESK[i] name. *)
Definition od_of (i : Z) : option desk := if i =? 1 then Some c24 else if i =? 2 then Some pc else None.

Lemma pd_of : forall i, 0 <= i < 3 -> pd_ok (pers_of i) (nth (Z.to_nat i) codec_SPEC_DESK 0) (od_of i).
Proof.
  intros i Hi. assert (E : i = 0 \/ i = 1 \/ i = 2) by lia.
  destruct E as [-> | [-> | ->]];
    [ left | right; left | right; right ]; (split; [ | split ]); reflexivity.
Qed.

(** ---- the reader switch (0x13368-0x13388) ---- *)

(** 0x13368 lw a0, kind; bltu s4 (13), a0 -> MASKS; else T1[kind] and jr. *)
Lemma head_dispatch : forall e fuel, env_ok e -> (forall kind, 0 <= kind <= 14 -> rd_ok e kind fuel) ->
  forall (ra' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' s8' s10' t3' t4' t5' t6' ops : word)
         (kind pv dv : Z) (od : option desk) (c rem : Z) (tl : list byte) (m : word -> option byte),
  0 <= kind <= 14 -> fuel_ok ops (S fuel) -> pd_ok pv dv od -> cur_ok e c rem ->
  rw_cells rsegs m (bv_unsigned (e_sp e) + -400) (body_cells e (k_rd kind pv dv) c rem tl) ->
  fr_ok e m ->
  evt rsegs (Qk e)
    (st e (body_regs e ra' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' (Z_to_bv 64 pv) ops s8' s10' t3' t4' t5' t6')
        0x13368 m).
Proof.
  intros e fuel HE RD ra' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' s8' s10' t3' t4' t5' t6' ops kind pv dv od
         c rem tl m HK HF HPD HC FB HFR.
  pose proof (bv_unsigned_in_range 64 (e_sp e)) as Rsp. unfold bv_modulus in Rsp.
  pose proof HE as (_ & _ & _ & HLO & _). unfold LLVM_CODEC_STACK in HLO.
  pose proof HFR as (_ & ST & _ & _ & HMI). pose proof ST as [Hlo0 _].
  assert (HKR : ov_read_bytes rsegs m (wa (bv_unsigned (e_sp e) + -384)) 4 = Some (le4 (Z_to_bv 64 kind))).
  { replace (bv_unsigned (e_sp e) + -384) with (bv_unsigned (e_sp e) + -400 + Z.of_nat 16) by lia.
    exact (rw_cells_read rsegs m _ _ 16 (C4 (Z_to_bv 64 kind)) FB eq_refl). }
  pose proof (codec_T1_at m HMI) as T1. unfold CODEC_T1, codec_T1_cells in T1.
  clear ST.
  unfold st, body_regs.
  zstep.
  rewrite (sx32_small kind) by lia.
  zstep.
  if_cases EB.
  - zify_cond EB. assert (kind = 14) by lia. subst kind.
    pose proof (RD 14 ltac:(lia)) as R. unfold rd_ok, st, body_regs in R.
    eapply R; [exact HF | exact HPD | exact HC | exact FB | exact HFR].
  - zify_cond EB.
    assert (E : kind = 0 \/ kind = 1 \/ kind = 2 \/ kind = 3 \/ kind = 4 \/ kind = 5 \/ kind = 6 \/ kind = 7 \/
                kind = 8 \/ kind = 9 \/ kind = 10 \/ kind = 11 \/ kind = 12 \/ kind = 13) by lia.
    clear EB HKR.
    destruct E as [E|[E|[E|[E|[E|[E|[E|[E|[E|[E|[E|[E|[E|E]]]]]]]]]]]]]; subst kind;
      do 7 zstep;
      (lazymatch goal with H : rw_cells _ _ _ (body_cells _ (k_rd ?k _ _) _ _ _) |- _ =>
         lazymatch goal with |- evt _ _ (MS _ _ ?pc _ _ _ _) =>
           replace pc with (Z_to_bv 64 (rd_pc k)) by (apply bv_eq; vm_compute; reflexivity) end;
         let R := fresh "R" in pose proof (RD k ltac:(lia)) as R; unfold rd_ok, st, body_regs in R;
         eapply R; [exact HF | exact HPD | exact HC | exact FB | exact HFR] end).
Qed.

(** ---- HEAD ---- *)

Lemma codec_main_head : S_head.
Proof.
  unfold S_head. intros CMS CPO e fuel HE RD.
  unfold memset_contract, MEMSET in CMS.
  unfold head_ok, st, body_regs.
  intros ra' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' s8' s10' t3' t4' t5' t6' ops c rem kj rj m1
         HF Hrem HC FR HFR.
  pose proof HE as (_ & _ & _ & HLO & _ & DJ & HPB & _). unfold LLVM_CODEC_STACK in HLO.
  pose proof (bv_unsigned_in_range 64 (e_sp e)) as Rsp. unfold bv_modulus in Rsp.
  pose proof (bv_unsigned_in_range 64 (e_p e)) as Rp. unfold bv_modulus in Rp.
  pose proof (data_of_fr e m1 HE HFR) as HD.
  destruct HFR as (SV & ST & MU & WM & HMI). unfold LLVM_CODEC_STACK in MU.
  pose proof ST as [Hlo0 _].
  pose proof HC as (Hc0 & Hr0 & Hcr).
  destruct (head_split e m1 c kj rj FR) as (FL & FK & FI). clear FR.
  assert (USP : bv_unsigned (Z_to_bv 64 (bv_unsigned (e_sp e) + -400)) = bv_unsigned (e_sp e) + -400)
    by (apply unsigned_lit; lia).
  assert (U384 : bv_unsigned (Z_to_bv 64 (bv_unsigned (e_sp e) + -384)) = bv_unsigned (e_sp e) + -384)
    by (apply unsigned_lit; lia).
  assert (U308 : bv_unsigned (Z_to_bv 64 (bv_unsigned (e_sp e) + -308)) = bv_unsigned (e_sp e) + -308)
    by (apply unsigned_lit; lia).
  assert (U184 : bv_unsigned (Z_to_bv 64 184) = 184) by (apply unsigned_lit; lia).
  assert (U64 : bv_unsigned (Z_to_bv 64 64) = 64) by (apply unsigned_lit; lia).
  zstep. zstep. zstep. zstep. zstep.
  match goal with HDm : bytes_at rsegs ?mm (bv_unsigned (e_p e)) (e_data e) |- _ =>
    destruct (byte_read_ex mm _ _ c HDm ltac:(lia)) as [b0 HB0] end.
  pose proof (bv_unsigned_in_range 8 b0) as Rb. unfold bv_modulus in Rb. change (2 ^ Z.of_N 8) with 256 in Rb.
  zstep.
  clear HB0.
  zstep. zstep. zstep. zstep.
  call CMS.
  { rewrite U384. exact FK. }
  { exact HMI. }
  rewrite ?USP, ?U384 in *.
  pose proof (memset_cells _ _ 0 184 ltac:(lia) ltac:(lia) POST) as FK0. clear POST.
  destruct (k0_split _ _ FK0) as (KLO & KAB & KHI). clear FK0.
  replace (bv_unsigned (e_sp e) + -384 + 76) with (bv_unsigned (e_sp e) + -308) in KAB by lia.
  replace (bv_unsigned (e_sp e) + -384 + 140) with (bv_unsigned (e_sp e) + -244) in KHI by lia.
  do 15 zstep.
  rewrite (land255_small (bv_unsigned b0)) by lia.
  rewrite (codec_div15_w (bv_unsigned b0)) by lia.
  rewrite (codec_div3_w (bv_unsigned b0 / 15)) by lia.
  rewrite !Z.shiftl_mul_pow2 by lia.
  rewrite (mod3_form (bv_unsigned b0 / 15)) by lia.
  match goal with HI : mem_inv rsegs ?mm |- _ =>
    pose proof (codec_DESK_read mm (bv_unsigned b0 / 15 mod 3) HI ltac:(lia)) as HDK end.
  unfold CODEC_DESK in HDK.
  zstep. zstep. zstep.
  rewrite (kind_form (bv_unsigned b0)) by lia.
  rewrite (sx32_small (bv_unsigned b0 / 15 mod 3)) by lia.
  clear HDK.
  zstep. zstep.
  unfold diginet_personality_of_contract, DIGINET_PERSONALITY_OF in CPO.
  eapply evt_cut; [ eapply CPO | intros ms' (a1x & a2x & ->) ].
  replace (ret_pc (Z_to_bv 64 0x13340)) with (Z_to_bv 64 0x13340)
    by (symmetry; apply ret_pc_even; [lia | reflexivity]).
  rewrite (unsigned_lit (bv_unsigned b0 / 15 mod 3)) by lia.
  pose proof (pers_of_range (bv_unsigned b0 / 15 mod 3)) as Rpv.
  pose proof (spec_desk_range (bv_unsigned b0 / 15 mod 3)) as Rdv.
  zstep. zstep. zstep.
  rewrite ?Z.shiftl_mul_pow2 by lia.
  match goal with M : munch _ (e_m e) ?mm |- _ =>
    pose proof (relro_of_munch e mm HE M) as HRL;
    pose proof (codec_SPEC_DESK_read mm (bv_unsigned b0 / 15 mod 3) HRL ltac:(lia)) as HSD end.
  unfold CODEC_SPEC_DESK in HSD. clear HRL.
  zstep.
  clear HSD.
  zstep. zstep. zstep. zstep. zstep. zstep.
  call CMS.
  { rewrite U308. exact KAB. }
  { assumption. }
  rewrite ?USP, ?U308 in *.
  pose proof (memset_cells _ _ 165 64 ltac:(lia) ltac:(lia) POST) as KA5. clear POST.
  apply a5_cells in KA5.
  replace (bv_unsigned (e_p e) + c + 1) with (bv_unsigned (e_p e) + (c + 1)) in FI by lia.
  replace (rem + -1) with (rem - 1) in FI by lia.
  pose proof (head_join e _ _ _ _ (c + 1) (rem - 1) (skipn 8 rj) FL KLO KA5 KHI FI) as FB.
  eapply (head_dispatch e fuel HE RD) with
    (kind := bv_unsigned b0 mod 15) (pv := pers_of (bv_unsigned b0 / 15 mod 3))
    (dv := nth (Z.to_nat (bv_unsigned b0 / 15 mod 3)) codec_SPEC_DESK 0) (od := od_of (bv_unsigned b0 / 15 mod 3))
    (c := c + 1) (rem := rem - 1) (tl := skipn 8 rj);
    [ | exact HF | apply pd_of; lia | | exact FB | ].
  - pose proof (Z.mod_pos_bound (bv_unsigned b0) 15 ltac:(lia)). lia.
  - unfold cur_ok. lia.
  - split; [exact SV|]. split; [exact ST|]. split; [exact MU|]. split; [exact WM|assumption].
Qed.
