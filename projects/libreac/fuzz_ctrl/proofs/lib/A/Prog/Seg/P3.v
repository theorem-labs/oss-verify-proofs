(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/jsoncons/fuzz_bigint/lib/L5TCopyS.v, with its module paths and module names changed; 1137 of its 1175 lines of code are new or changed and 210 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/B/Prog/reac_box_model_block.v; 1090 of its 1202 lines of code are new or changed and 1063 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/A/Prog/Seg/P5.v, with its addresses changed; 1324 of its 1487 lines of code are new or changed and 1039 lines of the source are left out. *)
(* Segment P3 of fuzz_ctrl LLVMFuzzerTestOneInput (asan, libreac v1.9.0 image A): [0x81b14, 0x81b7c],
   Inv_A81b14 -> Inv_A81b80 (v1.8 [0x81abc, 0x81afc], Inv_A81abc -> Inv_A81b00).  rule 24: no function proved (a slot
   segment).  S_P3 is CHANGED (new-call, new-insert); its v1.9 walk, with s3 = S(fr) (the shadow byte of the frame
   base), NEW-only instructions marked *:
     81b14-81b20  sb zero,336..339(s3); 81b24 li a0,6;
     81b28-81b34  sb zero,349..352(s3); 81b38* sb zero,353(s3); 81b3c* sb zero,354(s3);
     81b40* sb zero,360(s3); 81b44* sb zero,361(s3); 81b48* li a1,3;
     81b4c sb a0,340(s3); 81b50-81b58 sb zero,346..348(s3); 81b5c sb zero,362(s3); 81b60 sb zero,363(s3)
                  (v1.8 0x81af0 / 0x81af4 wrote 353 / 354); 81b64* sb a1,364(s3);
     81b68* li a2,35; 81b6c* ld a0,32(s1) (= fr + 2880, PRO's position 16); 81b70* li a1,0;
     81b74* jal checked_memset (__asan_memset@0x524c4): the 35 bytes of first.sroa.7 at fr + 2880 are zeroed;
     81b78 mv a0,s11; 81b7c jal reac_identity_init@0x87100 with s11 = fr + 2688.
   The 19 shadow stores write S(fr)+336 .. S(fr)+364 (29 bytes; 341..345 and 355..359 are kept): the 38 bytes of
   the local object at fr + 2688 (shadow 0,0,0,0,6), the 72 bytes at fragb fr = fr + 2768 (shadow 0 x 9) and the 35
   bytes of first.sroa.7 at fr + 2880 (shadow 0,0,0,0,3) are marked usable. The two calls run by their contracts
   asan_memset_contract and reac_identity_init_contract (hypotheses of seg_P3; linking happens later).  p3_evt is
   the Lib-level run of the 27 instructions and both calls.
   Both cuts are SlotInv's: the entry Inv_A81b14 and the exit Inv_A81b80 (seg_P3 : Hcut Inv_A81b80 -> Hcut
   Inv_A81b14).  No cut carries mem_inv (push 5d): p3_evt_ro runs p3_evt on the normalized memory from FRA's
   ro_agree (MemNorm.evt_normalize) and carries its post back to the real memory, the memory after the 19 stores
   included (p3_lift); ro_agree after the calls is MemNorm.ro_agree_same.  FRA moves across the stores by
   Tac_slot.sl_fr_meta, across the calls by Tac_slot.sl_fr_cl (the slot window by fl_stk, FSREC by
   fra_fsrec_stklo), and to the materialized model by sl_fra_move.  AH and the stack bounds after the stores and
   after the calls come per frame arm: Contract.a_laws_store on the real arm, a_laws_fs_store with
   Tac_fs.a_fs_ok_pres on the side arm.  ENT moves by ent_store over the whole write set, then ent_mat.  s1, s6 and
   s9 are unchanged (the run post keeps them, so CUR moves), and the run writes only frame shadow, the 35 bytes at
   fr + 2880, the 38 object bytes and the callee windows, so the cells the cuts name ([A + 144], [A + 192],
   [A + 280], [A + 240], fr + 2768, fr + 3040, fr + 3056, our[]) are kept.  The exit's IDBe g fr ID0 is made from
   the init post: the 38 object bytes at fr + 2688 are zero, which is ID0 = repeat (zb 0) 38.  Its addressable
   (fr + 2691) 17 is a sub-range of the 38 object bytes, which the shadow stores make addressable and the calls
   keep; its (cut bundle round 4) addressable (fr + 2880) 35 is made by the shadow stores 81b40 / 81b44 / 81b5c /
   81b60 / 81b64 and kept by the calls.  Aslot push 13: PRO moves by P1's pro_fra (no write is a PRO byte; our[]'s
   shadow byte S(fr) + 328 is below the stores at S(fr) + 336 .. S(fr) + 364).
   Copies: p3_run is a Theorem Labs lane's Seg/Tac_rt_b2.v sl_run_lib (P3 no longer imports Tac_rt_b2 / Tac_rt2_b2, though
   both are in this tree; it could be folded back).  The allocator laws are taken apart once
   each, in p3_laws_store / p3_laws_fs_place / p3_laws_fs_ok / p3_laws_fs_store.  P3 imports MemMono (rd_of_stk)
   instead of reac_box_model_block.
   v1.9 re-fit BUILT on v1.9 facts: rc=0 on a build machine workspace (internal path) (a copy of (internal path) at a working branch e3c0b7a9d6,
   FACTS ed6b6b7b0ab) with the cut base a working branch cf5ad0d7203, 2026-10-28. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac Bytes.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A Require Import Img0 AsanRT AsanRTFacts.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog Require Import asan_memset_c reac_identity_init_c.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog Require Import asan_memset_c_on.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require A.ShadowRwOn.
Import ListNotations.
Open Scope Z_scope.

(* The 29 frame-shadow bytes [S(fr) + 336, S(fr) + 365) after the 19 stores: b5..b9 (S(fr)+341 .. +345) and
   b19..b23 (S(fr)+355 .. +359) are kept. *)
Definition p3_shc (b5 b6 b7 b8 b9 b19 b20 b21 b22 b23 : byte) : list cell :=
  [C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 6);
   C1 b5; C1 b6; C1 b7; C1 b8; C1 b9;
   C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0);
   C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0);
   C1 b19; C1 b20; C1 b21; C1 b22; C1 b23;
   C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 3)].

Lemma p3_repeat_len : forall (x : byte) n, length (repeat x n) = n.
Proof. intros x n. induction n as [|n IH]; [reflexivity|]. cbn. rewrite IH. reflexivity. Qed.

Lemma p3_nth_repeat : forall (x : byte) n i, (i < n)%nat -> nth_error (repeat x n) i = Some x.
Proof.
  intros x n. induction n as [|n IH]; intros i Hi; [lia|].
  destruct i as [|i]; [reflexivity|]. cbn. apply IH. lia.
Qed.

(* k shadow bytes 0 at shadow_addr p (p 8-aligned): the 8k bytes at p are addressable. *)
Lemma p3_addr_zero : forall m p k, p mod 8 = 0 -> 0 <= k -> 0 <= p -> p + 8 * k <= APPMEM_END ->
  (forall i, 0 <= i < 8 * k -> app_mem (p + i)) ->
  bytes_at rsegs m (shadow_addr p) (repeat (Z_to_bv 8 0) (Z.to_nat k)) ->
  addressable m p (8 * k).
Proof.
  intros m p k Hp8 Hk Hp Hpk Happ HB.
  split; [lia|]. split; [lia|]. split; [lia|].
  intros i Hi. split; [apply Happ; lia|].
  assert (Esh : shadow_addr (p + i) = shadow_addr p + i / 8).
  { clear HB Happ. unfold shadow_addr. Z.div_mod_to_equations. lia. }
  exists (Z_to_bv 8 0). split; [| left; reflexivity].
  destruct HB as (_ & _ & HB).
  assert (Hj : (Z.to_nat (i / 8) < Z.to_nat k)%nat).
  { apply Z2Nat.inj_lt; [apply Z.div_pos; lia | lia | apply Z.div_lt_upper_bound; lia]. }
  pose proof (HB (Z.to_nat (i / 8)) ltac:(rewrite p3_repeat_len; exact Hj)) as HBj.
  rewrite Z2Nat.id in HBj by (apply Z.div_pos; lia).
  rewrite (p3_nth_repeat _ _ _ Hj) in HBj.
  rewrite Esh. exact HBj.
Qed.

(* One shadow byte r (0 < r < 8) at shadow_addr p (p 8-aligned): the r bytes at p are addressable. *)
Lemma p3_addr_part : forall m p r, p mod 8 = 0 -> 0 < r < 8 -> bv_signed (Z_to_bv 8 r) = r -> 0 <= p ->
  p + r <= APPMEM_END -> (forall i, 0 <= i < r -> app_mem (p + i)) ->
  bytes_at rsegs m (shadow_addr p) [Z_to_bv 8 r] -> addressable m p r.
Proof.
  intros m p r Hp8 Hr Hs Hp Hpr Happ HB.
  split; [lia|]. split; [lia|]. split; [lia|].
  intros i Hi. split; [apply Happ; lia|].
  assert (Esh : shadow_addr (p + i) = shadow_addr p).
  { clear HB Happ. unfold shadow_addr. Z.div_mod_to_equations. lia. }
  assert (Emod : (p + i) mod 8 = i).
  { clear HB Happ Esh. Z.div_mod_to_equations. lia. }
  exists (Z_to_bv 8 r). split.
  - rewrite Esh. destruct HB as (_ & _ & HB). specialize (HB 0%nat ltac:(cbn; lia)).
    cbn [Z.of_nat nth_error] in HB. rewrite Z.add_0_r in HB. exact HB.
  - unfold shadow_ok. right. rewrite Hs, Emod. lia.
Qed.

Lemma p3_addr_cat : forall m p n1 n2, addressable m p n1 -> addressable m (p + n1) n2 -> addressable m p (n1 + n2).
Proof.
  intros m p n1 n2 (H1 & H2 & H3 & H) (H1' & H2' & H3' & H').
  split; [lia|]. split; [lia|]. split; [lia|].
  intros i Hi. destruct (Z_lt_le_dec i n1) as [Hlt|Hge].
  - apply H. lia.
  - replace (p + i) with (p + n1 + (i - n1)) by lia. apply H'. lia.
Qed.

(* A sub-range of an addressable range is addressable. *)
Lemma p3_addr_sub : forall m p n k l, addressable m p n -> 0 <= k -> 0 <= l -> k + l <= n ->
  addressable m (p + k) l.
Proof.
  intros m p n k l (H1 & H2 & H3 & H) Hk Hl Hkl.
  split; [lia|]. split; [lia|]. split; [lia|].
  intros i Hi. replace (p + k + i) with (p + (k + i)) by lia. apply H. lia.
Qed.

(* Route (C) (a Theorem Labs lane's frozen form): every region present and writable at m still is at m' when the run writes
   only [lo, lo + n) and leaves those bytes readable.  No shadow byte is read: no premise. *)
Lemma p3_shadow_rw_keep_on : forall (m m' : word -> option byte) lo n bs,
  munch [(lo, lo + n)] m m' -> wmono rsegs m m' ->
  bytes_at rsegs m' lo bs -> Z.of_nat (length bs) = n ->
  forall P, A.ShadowRwOn.shadow_rw_on P m -> A.ShadowRwOn.shadow_rw_on P m'.
Proof.
  intros m m' lo n bs MU WM HB HL P HS a HPa Ha.
  destruct (HS a HPa Ha) as [Hw (b & Hb)]. split; [apply WM, Hw|].
  pose proof (in_shadow_range a Ha) as Hr.
  destruct (Z_lt_le_dec a lo) as [Hlt|Hge].
  - exists b. unfold mrd in *. rewrite (MU (wa a)); [exact Hb|].
    rewrite wa_unsigned by lia. cbn [outside]. split; [lia | exact I].
  - destruct (Z_lt_le_dec a (lo + n)) as [Hlt2|Hge2].
    + destruct HB as (_ & _ & HB). assert (Hi : (Z.to_nat (a - lo) < length bs)%nat) by lia.
      specialize (HB _ Hi). rewrite Z2Nat.id in HB by lia. replace (lo + (a - lo)) with a in HB by lia.
      rewrite HB. destruct (nth_error bs (Z.to_nat (a - lo))) eqn:E; [eexists; reflexivity|].
      apply nth_error_None in E. lia.
    + exists b. unfold mrd in *. rewrite (MU (wa a)); [exact Hb|].
      rewrite wa_unsigned by lia. cbn [outside]. split; [lia | exact I].
Qed.

(* shadow_rw survives a run that writes only [lo, lo + n) and leaves those bytes readable. *)
Lemma p3_shadow_rw_keep : forall (m m' : word -> option byte) lo n bs,
  shadow_rw m -> munch [(lo, lo + n)] m m' -> wmono rsegs m m' ->
  bytes_at rsegs m' lo bs -> Z.of_nat (length bs) = n -> shadow_rw m'.
Proof.
  intros m m' lo n bs HS MU WM HB HL. exact (A.ShadowRwOn.shadow_rw_of_on_all m' (p3_shadow_rw_keep_on m m' lo n bs
    MU WM HB HL (fun _ => True) (A.ShadowRwOn.shadow_rw_on_of_shadow_rw _ m HS))).
Qed.

(* One `sb` into the frame shadow: the step, then the stored byte as a C1 cell (0, 6 or 3) and the cell update. *)
Ltac p3_sb :=
  step;
  try (lazymatch goal with
       | |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ _ ?bs) _) =>
           first [ change bs with [Z_to_bv 8 0] | change bs with [Z_to_bv 8 6] | change bs with [Z_to_bv 8 3] ];
           mem_after_store
       end).

Lemma p3_evt : asan_memset_contract -> reac_identity_init_contract ->
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (spv S id lo A fb : Z)
         (b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 b16 b17 b18 b19 b20 b21 b22 b23 b24 b25 b26 b27
          b28 : byte) (idb fbj : list byte),
    sp = Z_to_bv 64 spv -> s3 = Z_to_bv 64 S -> s11 = Z_to_bv 64 id -> s1 = Z_to_bv 64 A ->
    0 <= spv < 2 ^ 64 -> 0 <= S -> RT_HI <= S -> S + 365 <= 2 ^ 64 -> S + 365 <= HIGHMEM_BEG ->
    0 < id -> id + 38 <= 2 ^ 64 -> id mod 2 = 0 ->
    (id + 38 <= S + 336 \/ S + 365 <= id) ->
    0 <= A -> A + 40 <= 2 ^ 64 -> (A + 40 <= S + 336 \/ S + 365 <= A + 32) ->
    0 < fb -> fb + 35 <= 2 ^ 64 -> (fb + 35 <= S + 336 \/ S + 365 <= fb) -> (fb + 35 <= id \/ id + 38 <= fb) ->
    rw_cells rsegs m (S + 336) [C1 b0; C1 b1; C1 b2; C1 b3; C1 b4; C1 b5; C1 b6; C1 b7; C1 b8; C1 b9;
                                C1 b10; C1 b11; C1 b12; C1 b13; C1 b14; C1 b15; C1 b16; C1 b17; C1 b18; C1 b19;
                                C1 b20; C1 b21; C1 b22; C1 b23; C1 b24; C1 b25; C1 b26; C1 b27; C1 b28] ->
    rw_cells rsegs m id [CB 38 idb] ->
    rw_cells rsegs m (A + 32) [C8 (Z_to_bv 64 fb)] ->
    rw_cells rsegs m fb [CB 35 fbj] ->
    (forall m', bytes_at rsegs m' (S + 336) [Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 6] ->
       addressable m' id 38) ->
    (forall m', bytes_at rsegs m' (S + 360) [Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 3] ->
       addressable m' fb 35) ->
    end_in_app id 38 -> (id + 38 <= RT_LO \/ RT_HI <= id) ->
    (id + 38 <= spv - REAC_IDENTITY_INIT_K \/ spv <= id) ->
    end_in_app fb 35 -> app_mem (fb + 7) -> (fb + 35 <= RT_LO \/ RT_HI <= fb) ->
    (fb + 35 <= spv - REAC_IDENTITY_INIT_K \/ spv <= fb) ->
    stk rsegs m lo spv -> lo + REAC_IDENTITY_INIT_K <= spv -> HIGHMEM_BEG <= lo -> spv <= APPMEM_END ->
    asan_cells m -> shadow_rw m -> mem_inv rsegs m ->
    evt rsegs
      (fun ms' => exists (R : bvmap 5 word) (msh m' : word -> option byte),
         ms' = MS R F (Z_to_bv 64 0x81b80) fc None m' (seg_rom rsegs) /\
         getr R 2 = sp /\ getr R 3 = gp /\ getr R 4 = tp /\ getr R 8 = s0 /\ getr R 9 = s1 /\
         getr R 19 = s3 /\ getr R 26 = s10 /\ getr R 22 = s6 /\ getr R 25 = s9 /\
         munch [(S + 336, S + 365)] m msh /\ wmono rsegs m msh /\
         rw_cells rsegs msh (S + 336) (p3_shc b5 b6 b7 b8 b9 b19 b20 b21 b22 b23) /\
         munch [(fb, fb + 35); (spv - REAC_IDENTITY_INIT_K, spv); (id, id + 38)] msh m' /\ wmono rsegs msh m' /\
         mem_inv rsegs m' /\ stk rsegs m' lo spv /\ asan_cells m' /\ shadow_rw m' /\
         rw_cells rsegs m' fb [CB 35 (repeat (Z_to_bv 8 0) 35)] /\
         rw_cells rsegs m' id [CB 38 (repeat (Z_to_bv 8 0) 38)])
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x81b14) fc None m (seg_rom rsegs)).
Proof.
  intros MSET RII ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m spv S id lo A fb b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 b16 b17 b18 b19 b20 b21 b22 b23
    b24 b25 b26 b27 b28 idb fbj
    -> -> -> -> Hspv HS0 HSRT HS64 HSHI Hid0 Hid38 Hidm HSEPs HA0 HA40 HSEPa Hfb0 Hfb35 HSEPb HSEPfi
    RWS RWI RWA RWF HADDR HADDRf HEI HRTI HSTI HEF HF7 HRTF HSTF ST HLO HHM HAE HAC HSW HMI.
  unfold asan_memset_contract, ASAN_MEMSET in MSET. cbv zeta in MSET.
  unfold reac_identity_init_contract, reac_identity_init_post, reac_identity_init_W, REAC_IDENTITY_INIT in RII.
  unfold REAC_IDENTITY_INIT_K in *.
  assert (EKm : ASAN_MEMSET_K = 2208) by reflexivity.
  pose proof (munch_refl [(S + 336, S + 365)] m) as MU0.
  pose proof (wmono_refl rsegs m) as WM0.
  (* 0x81b14 .. 0x81b64: the 19 shadow stores and the two li (the stored byte 3 at 81b64 is p3_sb's third case). *)
  p3_sb. p3_sb. p3_sb. p3_sb.                  (* 81b14 .. 81b20: S(fr) + 336 .. 339 *)
  step.                                        (* 81b24 li a0,6 *)
  p3_sb. p3_sb. p3_sb. p3_sb. p3_sb. p3_sb.    (* 81b28 .. 81b3c: 349 .. 354 (353 / 354 NEW-only) *)
  p3_sb. p3_sb.                                (* 81b40 / 81b44: 360 / 361 (NEW-only) *)
  step.                                        (* 81b48 li a1,3 (NEW-only) *)
  p3_sb. p3_sb. p3_sb. p3_sb.                  (* 81b4c .. 81b58: 340 (= 6), 346 .. 348 *)
  p3_sb. p3_sb. p3_sb.                         (* 81b5c / 81b60: 362 / 363; 81b64: 364 (= 3, NEW-only) *)
  (* 0x81b68 li a2,35 ; 0x81b6c ld a0,32(s1) ; 0x81b70 li a1,0 ; 0x81b74 jal checked_memset (all NEW-only) *)
  step. step. step. step.
  match goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => rename mm into msh end.
  assert (HB29 : bytes_at rsegs msh (S + 336) (cells_bytes (p3_shc b5 b6 b7 b8 b9 b19 b20 b21 b22 b23))).
  { destruct RWS as [[_ HB] _]. exact HB. }
  assert (HACs : asan_cells msh).
  { apply (asan_cells_kept [(S + 336, S + 365)] m msh HAC MU0). cbn [disjoint_from].
    unfold RT_LO, RT_HI in *. split; [lia | exact I]. }
  assert (HSWs : shadow_rw msh).
  { eapply (p3_shadow_rw_keep m msh (S + 336) 29 _ HSW); [| exact WM0 | exact HB29 | reflexivity].
    replace (S + 336 + 29) with (S + 365) by lia. exact MU0. }
  assert (HB5 : bytes_at rsegs msh (S + 336) [Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 6]).
  { assert (HB' : bytes_at rsegs msh (S + 336)
                    ([Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 6] ++
                     [b5; b6; b7; b8; b9; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0;
                      Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; b19; b20; b21; b22; b23;
                      Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 3])) by exact HB29.
    apply bytes_at_app in HB'. exact (proj1 HB'). }
  assert (HB360 : bytes_at rsegs msh (S + 360) [Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 3]).
  { assert (HB' : bytes_at rsegs msh (S + 336)
                    ([Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 6;
                      b5; b6; b7; b8; b9; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0;
                      Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; b19; b20; b21; b22; b23] ++
                     [Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 3])) by exact HB29.
    apply bytes_at_app in HB'. destruct HB' as [_ HB'].
    match type of HB' with bytes_at _ _ ?a _ => replace a with (S + 360) in HB' by (cbn; lia) end.
    exact HB'. }
  (* the memset of first.sroa.7 (new in v1.9): D = [s1 + 32] = fb, N = 35, a1 = 0; ld a0,32(s1) reads RWA. *)
  eapply evt_cut.
  { eapply MSET with (junk := fbj) (lo := lo).
    - rewrite !MState.unsigned_lit by lia. exact RWF.
    - rewrite !MState.unsigned_lit by lia. lia.
    - rewrite !MState.unsigned_lit by lia. exact (HADDRf msh HB360).
    - rewrite !MState.unsigned_lit by lia. exact HEF.
    - rewrite !MState.unsigned_lit by lia. right. exact HF7.
    - rewrite !MState.unsigned_lit by lia. exact HRTF.
    - rewrite !MState.unsigned_lit by lia. lia.
    - rewrite !MState.unsigned_lit by lia. exact ST.
    - rewrite !MState.unsigned_lit by lia. lia.
    - exact HHM.
    - rewrite !MState.unsigned_lit by lia. exact HAE.
    - exact HACs.
    - exact HSWs.
    - exact HMI. }
  intros ms' (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & mm &
              E & MUm & WMm & MIm & STm & RWm & HACm & HSWm).
  subst ms'.
  assert (Efb : bv_unsigned (Z_to_bv 64 fb) = fb) by (apply MState.unsigned_lit; lia).
  assert (E35 : bv_unsigned (Z_to_bv 64 35) = 35) by (apply MState.unsigned_lit; lia).
  assert (Esp : bv_unsigned (Z_to_bv 64 spv) = spv) by (apply MState.unsigned_lit; lia).
  rewrite Efb in MUm, RWm. rewrite E35 in MUm, RWm. rewrite Esp in MUm, STm.
  fold_lit_ux_in RWm.
  replace (ret_pc (Z_to_bv 64 0x81b78)) with (Z_to_bv 64 0x81b78)
    by (symmetry; apply ret_pc_even; [lia | reflexivity]).
  (* the identity record's cell and its 5 shadow bytes, past the memset ([fb, fb + 35) and its window) *)
  assert (RWI' : rw_cells rsegs mm id [CB 38 idb]).
  { apply (rw_cells_transport rsegs [(fb, fb + 35); (spv - ASAN_MEMSET_K, spv)] msh mm id _ RWI MUm WMm).
    cbn [disjoint_from cells_size csize]. repeat split; try exact I; lia. }
  assert (HB5m : bytes_at rsegs mm (S + 336) [Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 6]).
  { apply (bytes_at_transport rsegs [(fb, fb + 35); (spv - ASAN_MEMSET_K, spv)] msh mm (S + 336) _ HB5 MUm).
    cbn [disjoint_from length]. change (Z.of_nat 5) with 5. repeat split; try exact I; lia. }
  (* 0x81b78 mv a0,s11 ; 0x81b7c jal reac_identity_init *)
  step. step.
  eapply evt_cut.
  { eapply RII with (lo := lo) (id := id) (idb := idb).
    - first [reflexivity | f_equal; lia].
    - lia.
    - intros _. split; [exact Hidm | exact RWI'].
    - exact MIm.
    - rewrite MState.unsigned_lit by lia. exact STm.
    - rewrite MState.unsigned_lit by lia. lia.
    - exact HHM.
    - rewrite MState.unsigned_lit by lia. exact HAE.
    - exact HACm.
    - exact HSWm.
    - intros _. split; [exact (HADDR mm HB5m) | exact HEI].
    - intros _. exact HRTI.
    - intros _. rewrite MState.unsigned_lit by lia. exact HSTI. }
  intros ms' (t0'' & t1'' & t2'' & a1'' & a2'' & a3'' & a4'' & a5'' & a6'' & a7'' & t3'' & t4'' & t5'' & t6'' &
              m' & E & MUc & WMc & MIc & STc & HACc & HSWc & _ & RWc).
  subst ms'.
  rewrite Esp in MUc, STc.
  specialize (RWc ltac:(lia)).
  replace (ret_pc (Z_to_bv 64 0x81b80)) with (Z_to_bv 64 0x81b80)
    by (symmetry; apply ret_pc_even; [lia | reflexivity]).
  (* the two calls' write sets, joined: [spv - 2208, spv) is inside [spv - 2224, spv) *)
  assert (MUcall : munch [(fb, fb + 35); (spv - 2224, spv); (id, id + 38)] msh m').
  { apply (Frame.munch_trans _ msh mm m').
    - eapply Frame.munch_weaken; [| exact MUm]. intros x Hx. cbn [Frame.outside] in *.
      destruct Hx as (H1 & H2 & H3 & _). split; [exact H1|]. split; [|exact I]. intros Hc. apply H2. lia.
    - eapply Frame.munch_weaken; [| exact MUc]. intros x Hx. cbn [Frame.outside] in *.
      destruct Hx as (H1 & H2 & H3 & _). split; [exact H2|]. split; [exact H3 | exact I]. }
  assert (WMcall : wmono rsegs msh m') by (eapply Frame.wmono_trans; [exact WMm | exact WMc]).
  assert (RWF' : rw_cells rsegs m' fb [CB 35 (repeat (Z_to_bv 8 0) 35)]).
  { apply (rw_cells_transport rsegs [(spv - 2224, spv); (id, id + 38)] mm m' fb _ RWm MUc WMc).
    cbn [disjoint_from cells_size csize]. repeat split; try exact I; lia. }
  apply evt_done. do 3 eexists.
  split; [reflexivity|].
  split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
  split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
  split; [reflexivity|]. split; [reflexivity|].
  split; [exact MU0|]. split; [exact WM0|]. split; [exact RWS|].
  split; [exact MUcall|]. split; [exact WMcall|]. split; [exact MIc|].
  split; [exact STc|]. split; [exact HACc|]. split; [exact HSWc|].
  split; [exact RWF' | exact RWc].
Qed.

(* Route (C) (a Theorem Labs lane's frozen form; the 09:58Z ruling for a run with callee contracts: p3_evt stays as it is).
   The run reads no shadow byte; its 19 frame-shadow stores (0x81b14 .. 0x81b64) go through the rw_cells premise of
   S(fr)+336 .. +364, not through shadow_rw.  The shadow it needs is its two callees': the memset at 0x81b74
   (asan_memset_shadow_R at a0 = fb, a2 = 35) and reac_identity_init at 0x81b7c (reac_identity_init_shadow_R id). *)
Definition p3_evt_shadow_R (id fb : Z) : Z -> Prop :=
  fun a => asan_memset_shadow_R (Z_to_bv 64 fb) (Z_to_bv 64 35) a \/ reac_identity_init_shadow_R id a.

Lemma p3_evt_on : asan_memset_contract_on -> reac_identity_init_contract_on ->
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (spv S id lo A fb : Z)
         (b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 b16 b17 b18 b19 b20 b21 b22 b23 b24 b25 b26 b27
          b28 : byte) (idb fbj : list byte),
    sp = Z_to_bv 64 spv -> s3 = Z_to_bv 64 S -> s11 = Z_to_bv 64 id -> s1 = Z_to_bv 64 A ->
    0 <= spv < 2 ^ 64 -> 0 <= S -> RT_HI <= S -> S + 365 <= 2 ^ 64 -> S + 365 <= HIGHMEM_BEG ->
    0 < id -> id + 38 <= 2 ^ 64 -> id mod 2 = 0 ->
    (id + 38 <= S + 336 \/ S + 365 <= id) ->
    0 <= A -> A + 40 <= 2 ^ 64 -> (A + 40 <= S + 336 \/ S + 365 <= A + 32) ->
    0 < fb -> fb + 35 <= 2 ^ 64 -> (fb + 35 <= S + 336 \/ S + 365 <= fb) -> (fb + 35 <= id \/ id + 38 <= fb) ->
    rw_cells rsegs m (S + 336) [C1 b0; C1 b1; C1 b2; C1 b3; C1 b4; C1 b5; C1 b6; C1 b7; C1 b8; C1 b9;
                                C1 b10; C1 b11; C1 b12; C1 b13; C1 b14; C1 b15; C1 b16; C1 b17; C1 b18; C1 b19;
                                C1 b20; C1 b21; C1 b22; C1 b23; C1 b24; C1 b25; C1 b26; C1 b27; C1 b28] ->
    rw_cells rsegs m id [CB 38 idb] ->
    rw_cells rsegs m (A + 32) [C8 (Z_to_bv 64 fb)] ->
    rw_cells rsegs m fb [CB 35 fbj] ->
    (forall m', bytes_at rsegs m' (S + 336) [Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 6] ->
       addressable m' id 38) ->
    (forall m', bytes_at rsegs m' (S + 360) [Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 3] ->
       addressable m' fb 35) ->
    end_in_app id 38 -> (id + 38 <= RT_LO \/ RT_HI <= id) ->
    (id + 38 <= spv - REAC_IDENTITY_INIT_K \/ spv <= id) ->
    end_in_app fb 35 -> app_mem (fb + 7) -> (fb + 35 <= RT_LO \/ RT_HI <= fb) ->
    (fb + 35 <= spv - REAC_IDENTITY_INIT_K \/ spv <= fb) ->
    stk rsegs m lo spv -> lo + REAC_IDENTITY_INIT_K <= spv -> HIGHMEM_BEG <= lo -> spv <= APPMEM_END ->
    asan_cells m -> A.ShadowRwOn.shadow_rw_on (p3_evt_shadow_R id fb) m -> mem_inv rsegs m ->
    evt rsegs
      (fun ms' => exists (R : bvmap 5 word) (msh m' : word -> option byte),
         ms' = MS R F (Z_to_bv 64 0x81b80) fc None m' (seg_rom rsegs) /\
         getr R 2 = sp /\ getr R 3 = gp /\ getr R 4 = tp /\ getr R 8 = s0 /\ getr R 9 = s1 /\
         getr R 19 = s3 /\ getr R 26 = s10 /\ getr R 22 = s6 /\ getr R 25 = s9 /\
         munch [(S + 336, S + 365)] m msh /\ wmono rsegs m msh /\
         rw_cells rsegs msh (S + 336) (p3_shc b5 b6 b7 b8 b9 b19 b20 b21 b22 b23) /\
         munch [(fb, fb + 35); (spv - REAC_IDENTITY_INIT_K, spv); (id, id + 38)] msh m' /\ wmono rsegs msh m' /\
         mem_inv rsegs m' /\ stk rsegs m' lo spv /\ asan_cells m' /\
         (forall P, A.ShadowRwOn.shadow_rw_on P m -> A.ShadowRwOn.shadow_rw_on P m') /\
         rw_cells rsegs m' fb [CB 35 (repeat (Z_to_bv 8 0) 35)] /\
         rw_cells rsegs m' id [CB 38 (repeat (Z_to_bv 8 0) 38)])
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x81b14) fc None m (seg_rom rsegs)).
Proof.
  intros MSET RII ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m spv S id lo A fb b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 b16 b17 b18 b19 b20 b21 b22 b23
    b24 b25 b26 b27 b28 idb fbj
    -> -> -> -> Hspv HS0 HSRT HS64 HSHI Hid0 Hid38 Hidm HSEPs HA0 HA40 HSEPa Hfb0 Hfb35 HSEPb HSEPfi
    RWS RWI RWA RWF HADDR HADDRf HEI HRTI HSTI HEF HF7 HRTF HSTF ST HLO HHM HAE HAC HSW HMI.
  unfold asan_memset_contract_on, ASAN_MEMSET in MSET. cbv zeta in MSET.
  unfold reac_identity_init_contract_on, reac_identity_init_post_on, reac_identity_init_W, REAC_IDENTITY_INIT in RII.
  unfold REAC_IDENTITY_INIT_K in *.
  assert (EKm : ASAN_MEMSET_K = 2208) by reflexivity.
  pose proof (munch_refl [(S + 336, S + 365)] m) as MU0.
  pose proof (wmono_refl rsegs m) as WM0.
  (* 0x81b14 .. 0x81b64: the 19 shadow stores and the two li (the stored byte 3 at 81b64 is p3_sb's third case). *)
  p3_sb. p3_sb. p3_sb. p3_sb.                  (* 81b14 .. 81b20: S(fr) + 336 .. 339 *)
  step.                                        (* 81b24 li a0,6 *)
  p3_sb. p3_sb. p3_sb. p3_sb. p3_sb. p3_sb.    (* 81b28 .. 81b3c: 349 .. 354 (353 / 354 NEW-only) *)
  p3_sb. p3_sb.                                (* 81b40 / 81b44: 360 / 361 (NEW-only) *)
  step.                                        (* 81b48 li a1,3 (NEW-only) *)
  p3_sb. p3_sb. p3_sb. p3_sb.                  (* 81b4c .. 81b58: 340 (= 6), 346 .. 348 *)
  p3_sb. p3_sb. p3_sb.                         (* 81b5c / 81b60: 362 / 363; 81b64: 364 (= 3, NEW-only) *)
  (* 0x81b68 li a2,35 ; 0x81b6c ld a0,32(s1) ; 0x81b70 li a1,0 ; 0x81b74 jal checked_memset (all NEW-only) *)
  step. step. step. step.
  match goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => rename mm into msh end.
  assert (HB29 : bytes_at rsegs msh (S + 336) (cells_bytes (p3_shc b5 b6 b7 b8 b9 b19 b20 b21 b22 b23))).
  { destruct RWS as [[_ HB] _]. exact HB. }
  assert (HACs : asan_cells msh).
  { apply (asan_cells_kept [(S + 336, S + 365)] m msh HAC MU0). cbn [disjoint_from].
    unfold RT_LO, RT_HI in *. split; [lia | exact I]. }
  assert (KPs : forall P, A.ShadowRwOn.shadow_rw_on P m -> A.ShadowRwOn.shadow_rw_on P msh).
  { intros P HP. eapply (p3_shadow_rw_keep_on m msh (S + 336) 29 _); [| exact WM0 | exact HB29 | reflexivity | exact HP].
    replace (S + 336 + 29) with (S + 365) by lia. exact MU0. }
  assert (HB5 : bytes_at rsegs msh (S + 336) [Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 6]).
  { assert (HB' : bytes_at rsegs msh (S + 336)
                    ([Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 6] ++
                     [b5; b6; b7; b8; b9; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0;
                      Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; b19; b20; b21; b22; b23;
                      Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 3])) by exact HB29.
    apply bytes_at_app in HB'. exact (proj1 HB'). }
  assert (HB360 : bytes_at rsegs msh (S + 360) [Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 3]).
  { assert (HB' : bytes_at rsegs msh (S + 336)
                    ([Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 6;
                      b5; b6; b7; b8; b9; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0;
                      Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; b19; b20; b21; b22; b23] ++
                     [Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 3])) by exact HB29.
    apply bytes_at_app in HB'. destruct HB' as [_ HB'].
    match type of HB' with bytes_at _ _ ?a _ => replace a with (S + 360) in HB' by (cbn; lia) end.
    exact HB'. }
  (* the memset of first.sroa.7 (new in v1.9): D = [s1 + 32] = fb, N = 35, a1 = 0; ld a0,32(s1) reads RWA. *)
  eapply evt_cut.
  { eapply MSET with (junk := fbj) (lo := lo).
    - rewrite !MState.unsigned_lit by lia. exact RWF.
    - rewrite !MState.unsigned_lit by lia. lia.
    - rewrite !MState.unsigned_lit by lia. exact (HADDRf msh HB360).
    - rewrite !MState.unsigned_lit by lia. exact HEF.
    - rewrite !MState.unsigned_lit by lia. right. exact HF7.
    - rewrite !MState.unsigned_lit by lia. exact HRTF.
    - rewrite !MState.unsigned_lit by lia. lia.
    - rewrite !MState.unsigned_lit by lia. exact ST.
    - rewrite !MState.unsigned_lit by lia. lia.
    - exact HHM.
    - rewrite !MState.unsigned_lit by lia. exact HAE.
    - exact HACs.
    - apply (A.ShadowRwOn.shadow_rw_on_mono (p3_evt_shadow_R id fb)); [|exact (KPs _ HSW)].
      intros x Hx. unfold p3_evt_shadow_R. left. exact Hx.
    - exact HMI. }
  intros ms' (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & mm &
              E & MUm & WMm & MIm & STm & RWm & HACm & HSWm).
  subst ms'.
  assert (Efb : bv_unsigned (Z_to_bv 64 fb) = fb) by (apply MState.unsigned_lit; lia).
  assert (E35 : bv_unsigned (Z_to_bv 64 35) = 35) by (apply MState.unsigned_lit; lia).
  assert (Esp : bv_unsigned (Z_to_bv 64 spv) = spv) by (apply MState.unsigned_lit; lia).
  rewrite Efb in MUm, RWm. rewrite E35 in MUm, RWm. rewrite Esp in MUm, STm.
  fold_lit_ux_in RWm.
  replace (ret_pc (Z_to_bv 64 0x81b78)) with (Z_to_bv 64 0x81b78)
    by (symmetry; apply ret_pc_even; [lia | reflexivity]).
  (* the identity record's cell and its 5 shadow bytes, past the memset ([fb, fb + 35) and its window) *)
  assert (RWI' : rw_cells rsegs mm id [CB 38 idb]).
  { apply (rw_cells_transport rsegs [(fb, fb + 35); (spv - ASAN_MEMSET_K, spv)] msh mm id _ RWI MUm WMm).
    cbn [disjoint_from cells_size csize]. repeat split; try exact I; lia. }
  assert (HB5m : bytes_at rsegs mm (S + 336) [Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 6]).
  { apply (bytes_at_transport rsegs [(fb, fb + 35); (spv - ASAN_MEMSET_K, spv)] msh mm (S + 336) _ HB5 MUm).
    cbn [disjoint_from length]. change (Z.of_nat 5) with 5. repeat split; try exact I; lia. }
  (* 0x81b78 mv a0,s11 ; 0x81b7c jal reac_identity_init *)
  step. step.
  eapply evt_cut.
  { eapply RII with (lo := lo) (id := id) (idb := idb).
    - first [reflexivity | f_equal; lia].
    - lia.
    - intros _. split; [exact Hidm | exact RWI'].
    - exact MIm.
    - rewrite MState.unsigned_lit by lia. exact STm.
    - rewrite MState.unsigned_lit by lia. lia.
    - exact HHM.
    - rewrite MState.unsigned_lit by lia. exact HAE.
    - exact HACm.
    - apply (A.ShadowRwOn.shadow_rw_on_mono (p3_evt_shadow_R id fb)); [|exact (HSWm _ (KPs _ HSW))].
      intros x Hx. unfold p3_evt_shadow_R. right. exact Hx.
    - intros _. split; [exact (HADDR mm HB5m) | exact HEI].
    - intros _. exact HRTI.
    - intros _. rewrite MState.unsigned_lit by lia. exact HSTI. }
  intros ms' (t0'' & t1'' & t2'' & a1'' & a2'' & a3'' & a4'' & a5'' & a6'' & a7'' & t3'' & t4'' & t5'' & t6'' &
              m' & E & MUc & WMc & MIc & STc & HACc & HSWc & _ & RWc).
  subst ms'.
  rewrite Esp in MUc, STc.
  specialize (RWc ltac:(lia)).
  replace (ret_pc (Z_to_bv 64 0x81b80)) with (Z_to_bv 64 0x81b80)
    by (symmetry; apply ret_pc_even; [lia | reflexivity]).
  (* the two calls' write sets, joined: [spv - 2208, spv) is inside [spv - 2224, spv) *)
  assert (MUcall : munch [(fb, fb + 35); (spv - 2224, spv); (id, id + 38)] msh m').
  { apply (Frame.munch_trans _ msh mm m').
    - eapply Frame.munch_weaken; [| exact MUm]. intros x Hx. cbn [Frame.outside] in *.
      destruct Hx as (H1 & H2 & H3 & _). split; [exact H1|]. split; [|exact I]. intros Hc. apply H2. lia.
    - eapply Frame.munch_weaken; [| exact MUc]. intros x Hx. cbn [Frame.outside] in *.
      destruct Hx as (H1 & H2 & H3 & _). split; [exact H2|]. split; [exact H3 | exact I]. }
  assert (WMcall : wmono rsegs msh m') by (eapply Frame.wmono_trans; [exact WMm | exact WMc]).
  assert (RWF' : rw_cells rsegs m' fb [CB 35 (repeat (Z_to_bv 8 0) 35)]).
  { apply (rw_cells_transport rsegs [(spv - 2224, spv); (id, id + 38)] mm m' fb _ RWm MUc WMc).
    cbn [disjoint_from cells_size csize]. repeat split; try exact I; lia. }
  apply evt_done. do 3 eexists.
  split; [reflexivity|].
  split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
  split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
  split; [reflexivity|]. split; [reflexivity|].
  split; [exact MU0|]. split; [exact WM0|]. split; [exact RWS|].
  split; [exact MUcall|]. split; [exact WMcall|]. split; [exact MIc|].
  split; [exact STc|]. split; [exact HACc|]. split; [intros P HP; exact (HSWc P (HSWm P (KPs P HP)))|].
  split; [exact RWF' | exact RWc].
Qed.

(* ---- The wrapper seg_P3.  The run is p3_run (a copy of a Theorem Labs lane's Seg/Tac_rt_b2.v sl_run_lib) feeding
   p3_evt_ro. ---- *)
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Reusable Require Import YK11 YM05 YK0o YK0s YK15 YP09 YO0f YO0d YO09
  YL00 YL0g YL0i YI14 YI16 YL01 YM06.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require MState Regs6ss RegisterBridge.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A Require Import AsanRTInv PContract MemNorm AsanLift BzBridge KindBGlue.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A Require Contract FrameAPI.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require A.ShadowRwOnT.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog Require Import SlotModel SlotInv RcAsanFPLib.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog Require Import MemMono.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog.Seg Require Import Tac_slot Tac_fs P1.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog.Seg Require Tac_b5.
Import OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Reusable.YK11.
Open Scope Z_scope.

Module ACw := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Contract.
Module AFw := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.FrameAPI.
Module LM := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Mem.
Module LE := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Exec.

(* p3_run: a copy of a Theorem Labs lane's Seg/Tac_rt_b2.v sl_run_lib (in this tree), word for word but for the name and the module path of
   Exec.evt (here LE.evt: in this file a later import shadows the short name Exec), so that P3 does not import
   Tac_rt_b2 / Tac_rt2_b2. The Lib-evt -> SR bridge for a segment that calls a callee: the run
   is closed to SR by AsanLift.evt_SR_canon_lazy. *)
Section R3.
Context {fx : FPState}.

Lemma p3_run : forall regs pc mem md
  (K : bvmap 5 word -> word -> (word -> option byte) -> Prop) (P : config -> Prop),
  m_halted md = None ->
  LE.evt rsegs
    (fun ms => exists R pc' mem', ms = MState.MS R fp_regs pc' fp_csr None mem' (seg_rom rsegs) /\ K R pc' mem')
    (RegisterBridge.canonical_register_state (mkst regs pc mem (seg_rom rsegs))) ->
  (forall R pc' mem' regs' md', K R pc' mem' -> (forall r, getr regs' r = getr R r) -> AsanLift.mat_le md md' ->
     SR rsegs (mkCfg (mkst regs' pc' mem' (seg_rom rsegs)) md') P) ->
  SR rsegs (mkCfg (mkst regs pc mem (seg_rom rsegs)) md) P.
Proof.
  intros regs pc mem md K P Hh HE HK.
  eapply (AsanLift.evt_SR_canon_lazy rsegs (mkst regs pc mem (seg_rom rsegs)) _ md P); [exact HE | exact Hh |].
  intros ms' md' (can & (R & pc' & mem' & -> & HKR) & Heq) Hmat.
  destruct Heq as (HR & HF & Hpc & Hsvc & Hres & Hfc & Hm & Hrom).
  destruct ms' as [regs' fr' pcv' svc' rv' fc' m' ro'].
  cbn in HR, HF, Hpc, Hsvc, Hres, Hfc, Hm, Hrom. subst.
  apply (HK R _ _ regs' md' HKR); [apply kb_getr_eqv; exact HR | exact Hmat].
Qed.

End R3.

(* ---- The call on the normalized memory (push 5d: no cut carries mem_inv).  The image's segments all end at or
   below 0x5fe000, so no byte at or above it is read-only and MemNorm.normalize leaves it alone (Seg/P6.v's
   p6_ro_addr_hi); every fact p3_evt reads or gives is about such bytes or is a bytes_at fact. ---- *)
Definition p3_tops (segs : list Segment) (top : Z) : bool :=
  forallb (fun s => Z.of_N (seg_base s) + Z.of_N (seg_size s) <=? top) segs.

Lemma p3_rsegs_below_gt : p3_tops rsegs 0x5fe000 = true.
Proof. vm_compute. reflexivity. Qed.

Lemma p3_find_below : forall segs top x n s,
  p3_tops segs top = true -> find_segment segs x n = Some s -> 0 <= n -> x < top \/ n = 0.
Proof.
  induction segs as [|s0 r IH]; intros top x n s Hb H Hn; cbn in H; [discriminate H|].
  unfold p3_tops in Hb. cbn [forallb] in Hb. apply andb_prop in Hb as [H0 Hr].
  apply Z.leb_le in H0.
  destruct (Z.leb (Z.of_N (seg_base s0)) x && Z.leb (x + n) (Z.of_N (seg_base s0) + Z.of_N (seg_size s0))) eqn:E.
  - apply andb_prop in E as [_ E]. apply Z.leb_le in E. lia.
  - exact (IH top x n s Hr H Hn).
Qed.

Lemma p3_ro_hi : forall a, 0x5fe000 <= a < 2 ^ 64 -> LM.ro_addr rsegs (wa a) = false.
Proof.
  intros a Ha. unfold LM.ro_addr.
  match goal with |- context [find_segment ?sg ?x ?n] =>
    destruct (find_segment sg x n) as [s|] eqn:E; [|reflexivity];
    destruct (p3_find_below sg 0x5fe000 x n s p3_rsegs_below_gt E ltac:(cbn; lia)) as [L|L];
    [exfalso; rewrite MState.unsigned_lit in L by lia; lia | cbn in L; lia] end.
Qed.

(* Every MemNorm name below is written by its full path to image A's copy lib.A.MemNorm (one image, one MemNorm
   copy: a Theorem Labs lane 07:07Z), so the text names that copy whether or not BzBridge also loads the root lib.MemNorm. *)
Lemma p3_wview_rel_hi : forall m m0 a,
  OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.MemNorm.mem_rel rsegs m m0 -> 0x5fe000 <= a < 2 ^ 64 ->
  (wview rsegs m0 (wa a) <> None <-> wview rsegs m (wa a) <> None).
Proof.
  intros m m0 a HR Ha.
  rewrite (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.MemNorm.wview_rel_rw rsegs m m0 (wa a) HR (p3_ro_hi a Ha)).
  split; auto.
Qed.

Lemma p3_stk_rel : forall m m0 lo hi,
  OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.MemNorm.mem_rel rsegs m m0 -> 0x5fe000 <= lo -> hi <= 2 ^ 64 ->
  stk rsegs m lo hi -> stk rsegs m0 lo hi.
Proof.
  intros m m0 lo hi HR Hlo Hhi (H0 & H1 & H). split; [lia|]. split; [lia|]. intros a Ha.
  destruct (H a Ha) as (Hw & b & Hb). split.
  - apply (proj2 (p3_wview_rel_hi m m0 a HR ltac:(lia))). exact Hw.
  - exists b. rewrite <- (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.MemNorm.mrd_rel rsegs m m0 (wa a) HR).
    exact Hb.
Qed.

Lemma p3_stk_back : forall m m0 lo hi,
  OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.MemNorm.mem_rel rsegs m m0 -> 0x5fe000 <= lo -> hi <= 2 ^ 64 ->
  stk rsegs m0 lo hi -> stk rsegs m lo hi.
Proof.
  intros m m0 lo hi HR Hlo Hhi (H0 & H1 & H). split; [lia|]. split; [lia|]. intros a Ha.
  destruct (H a Ha) as (Hw & b & Hb). split.
  - apply (proj1 (p3_wview_rel_hi m m0 a HR ltac:(lia))). exact Hw.
  - exists b. rewrite (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.MemNorm.mrd_rel rsegs m m0 (wa a) HR).
    exact Hb.
Qed.

Lemma p3_rw_rel : forall m m0 A cs,
  OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.MemNorm.mem_rel rsegs m m0 -> 0x5fe000 <= A ->
  rw_cells rsegs m A cs -> rw_cells rsegs m0 A cs.
Proof.
  intros m m0 A cs R HA [[Hwf HB] (H0 & H1 & HW)].
  split; [split; [exact Hwf |
                  exact (proj1 (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.MemNorm.bytes_at_rel rsegs m m0 A _ R)
                           HB)]|].
  split; [exact H0|]. split; [exact H1|]. intros i Hi.
  rewrite (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.MemNorm.wview_rel_rw rsegs m m0 _ R
             (p3_ro_hi (A + i) ltac:(lia))).
  exact (HW i Hi).
Qed.

Lemma p3_rw_back : forall m m0 A cs,
  OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.MemNorm.mem_rel rsegs m m0 -> 0x5fe000 <= A ->
  rw_cells rsegs m0 A cs -> rw_cells rsegs m A cs.
Proof.
  intros m m0 A cs R HA [[Hwf HB] (H0 & H1 & HW)].
  split; [split; [exact Hwf |
                  exact (proj2 (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.MemNorm.bytes_at_rel rsegs m m0 A _ R)
                           HB)]|].
  split; [exact H0|]. split; [exact H1|]. intros i Hi.
  rewrite <- (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.MemNorm.wview_rel_rw rsegs m m0 _ R
                (p3_ro_hi (A + i) ltac:(lia))).
  exact (HW i Hi).
Qed.

Lemma p3_cells_rel : forall m m0,
  OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.MemNorm.mem_rel rsegs m m0 -> asan_cells m -> asan_cells m0.
Proof.
  intros m m0 REL HAC. unfold asan_cells in HAC |- *.
  repeat match goal with H : _ /\ _ |- _ => destruct H end.
  repeat match goal with |- _ /\ _ => split end;
    apply (proj1 (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.MemNorm.bytes_at_rel rsegs m m0 _ _ REL));
    assumption.
Qed.

Lemma p3_shadow_rw_rel : forall m m0,
  OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.MemNorm.mem_rel rsegs m m0 -> shadow_rw m -> shadow_rw m0.
Proof.
  intros m m0 REL HSW a Ha. pose proof (Tac_b5.sl_shadow_not_ro a Ha) as Hro.
  destruct (HSW a Ha) as (Hw & b & Hb). split.
  - rewrite (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.MemNorm.wview_rel_rw rsegs m m0 (wa a) REL Hro).
    exact Hw.
  - exists b. rewrite <- (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.MemNorm.mrd_rel rsegs m m0 (wa a) REL).
    exact Hb.
Qed.

(* The real memory after the 19 stores, rebuilt from the normalized one: the read-only bytes of the entry memory m,
   every other byte of the normalized run's memory m0. *)
Definition p3_lift (m m0 : word -> option byte) : word -> option byte :=
  fun a => if LM.ro_addr rsegs a then m a else m0 a.

(* p3_evt from ro_agree instead of mem_inv: the run on the normalized memory, carried back by
   MemNorm.evt_normalize (as P1's p1_evt_ro / P6's p6_evt_ro).  The memory after the stores is p3_lift of the
   entry memory and the normalized one, which is related to it by mem_rel and has the entry memory's read-only
   bytes, so both munch / wmono facts cross by munch_rel / wmono_rel. *)
Lemma p3_evt_ro : asan_memset_contract -> reac_identity_init_contract ->
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (spv S id lo A fb : Z)
         (b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 b16 b17 b18 b19 b20 b21 b22 b23 b24 b25 b26 b27
          b28 : byte) (idb fbj : list byte),
    sp = Z_to_bv 64 spv -> s3 = Z_to_bv 64 S -> s11 = Z_to_bv 64 id -> s1 = Z_to_bv 64 A ->
    0 <= spv < 2 ^ 64 -> LOWMEM_END <= S -> S + 365 <= HIGHMEM_BEG ->
    0x5fe000 <= id -> id + 38 <= 2 ^ 64 -> id mod 2 = 0 ->
    (id + 38 <= S + 336 \/ S + 365 <= id) ->
    0x5fe000 <= A -> A + 40 <= 2 ^ 64 -> (A + 40 <= S + 336 \/ S + 365 <= A + 32) ->
    0x5fe000 <= fb -> fb + 35 <= 2 ^ 64 -> (fb + 35 <= S + 336 \/ S + 365 <= fb) ->
    (fb + 35 <= id \/ id + 38 <= fb) ->
    rw_cells rsegs m (S + 336) [C1 b0; C1 b1; C1 b2; C1 b3; C1 b4; C1 b5; C1 b6; C1 b7; C1 b8; C1 b9;
                                C1 b10; C1 b11; C1 b12; C1 b13; C1 b14; C1 b15; C1 b16; C1 b17; C1 b18; C1 b19;
                                C1 b20; C1 b21; C1 b22; C1 b23; C1 b24; C1 b25; C1 b26; C1 b27; C1 b28] ->
    rw_cells rsegs m id [CB 38 idb] ->
    rw_cells rsegs m (A + 32) [C8 (Z_to_bv 64 fb)] ->
    rw_cells rsegs m fb [CB 35 fbj] ->
    (forall m', bytes_at rsegs m' (S + 336) [Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 6] ->
       addressable m' id 38) ->
    (forall m', bytes_at rsegs m' (S + 360) [Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 3] ->
       addressable m' fb 35) ->
    end_in_app id 38 -> (id + 38 <= RT_LO \/ RT_HI <= id) ->
    (id + 38 <= spv - REAC_IDENTITY_INIT_K \/ spv <= id) ->
    end_in_app fb 35 -> app_mem (fb + 7) -> (fb + 35 <= RT_LO \/ RT_HI <= fb) ->
    (fb + 35 <= spv - REAC_IDENTITY_INIT_K \/ spv <= fb) ->
    stk rsegs m lo spv -> lo + REAC_IDENTITY_INIT_K <= spv -> HIGHMEM_BEG <= lo -> spv <= APPMEM_END ->
    asan_cells m -> shadow_rw m -> OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.MemNorm.ro_agree rsegs m ->
    evt rsegs
      (fun ms' => exists (R : bvmap 5 word) (msh m' : word -> option byte),
         ms' = MS R F (Z_to_bv 64 0x81b80) fc None m' (seg_rom rsegs) /\
         getr R 2 = sp /\ getr R 3 = gp /\ getr R 4 = tp /\ getr R 8 = s0 /\ getr R 9 = s1 /\
         getr R 19 = s3 /\ getr R 26 = s10 /\ getr R 22 = s6 /\ getr R 25 = s9 /\
         munch [(S + 336, S + 365)] m msh /\ wmono rsegs m msh /\
         rw_cells rsegs msh (S + 336) (p3_shc b5 b6 b7 b8 b9 b19 b20 b21 b22 b23) /\
         munch [(fb, fb + 35); (spv - REAC_IDENTITY_INIT_K, spv); (id, id + 38)] msh m' /\ wmono rsegs msh m' /\
         OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.MemNorm.ro_agree rsegs m' /\ stk rsegs m' lo spv /\
         rw_cells rsegs m' fb [CB 35 (repeat (Z_to_bv 8 0) 35)] /\
         rw_cells rsegs m' id [CB 38 (repeat (Z_to_bv 8 0) 38)])
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x81b14) fc None m (seg_rom rsegs)).
Proof.
  intros MSET RII ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m spv S id lo A fb b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 b16 b17 b18 b19 b20 b21 b22 b23
    b24 b25 b26 b27 b28 idb fbj
    E2 E19 E27 E9 Hspv HSlo HSHI Hid0 Hid38 Hidm HSEPs HA0 HA40 HSEPa Hfb0 Hfb35 HSEPb HSEPfi
    RWS RWI RWA RWF HADDR HADDRf HEI HRTI HSTI HEF HF7 HRTF HSTF ST HLO HHM HAE HAC HSW HRO.
  assert (EL : LOWMEM_END = 2147450880) by reflexivity.
  assert (EH : HIGHMEM_BEG = 17594333495296) by reflexivity.
  assert (ERT : RT_HI = 0xa9578) by reflexivity.
  pose proof (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.MemNorm.mem_rel_normalize rsegs m HRO) as REL.
  eapply evt_mono.
  - eapply OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.MemNorm.evt_normalize;
      [vm_compute; reflexivity | exact HRO |].
    apply (p3_evt MSET RII ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4
             t5 t6 F fc (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.MemNorm.normalize rsegs m) spv S id lo A fb
             b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13
             b14 b15 b16 b17 b18 b19 b20 b21 b22 b23 b24 b25 b26 b27 b28 idb fbj E2 E19 E27 E9 Hspv ltac:(lia)
             ltac:(lia) ltac:(lia) HSHI ltac:(lia) Hid38 Hidm HSEPs ltac:(lia) HA40 HSEPa ltac:(lia) Hfb35 HSEPb
             HSEPfi
             (p3_rw_rel m _ (S + 336) _ REL ltac:(lia) RWS) (p3_rw_rel m _ id _ REL ltac:(lia) RWI)
             (p3_rw_rel m _ (A + 32) _ REL ltac:(lia) RWA) (p3_rw_rel m _ fb _ REL ltac:(lia) RWF)
             HADDR HADDRf HEI HRTI HSTI HEF HF7 HRTF HSTF
             (p3_stk_rel m _ lo spv REL ltac:(lia) ltac:(lia) ST) HLO HHM HAE (p3_cells_rel m _ REL HAC)
             (p3_shadow_rw_rel m _ REL HSW)
             (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.MemNorm.mem_inv_normalize rsegs m)).
  - intros s (s0' & (R & msh0 & m0' & -> & P2 & P3 & P4 & P8 & P9 & P19 & P26 & P22 & P25 & MU1 & WM1 & RWS1 &
               MU2 & WM2 & _ & ST2 & _ & _ & RWF2 & RW2) & MR & RS).
    destruct MR as (HR & HF & Hpc & Hsvc & Hres & Hfc & Hrom & Hmem).
    destruct s as [Rs Fs pcs svcs rvs fcs ms ros].
    cbn in HR, HF, Hpc, Hsvc, Hres, Hfc, Hrom, Hmem, RS. subst Rs Fs pcs svcs rvs fcs ros.
    assert (RELsh : OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.MemNorm.mem_rel rsegs (p3_lift m msh0) msh0).
    { split.
      - intros a. unfold OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.MemNorm.normalize, p3_lift.
        destruct (LM.ro_addr rsegs a) eqn:E; [|reflexivity].
        rewrite (MU1 a).
        + unfold OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.MemNorm.normalize. rewrite E. reflexivity.
        + pose proof (Tac_b5.sl_ro_lo a E) as Ha. cbn [Frame.outside]. split; [lia | exact I].
      - intros a b E Hb. unfold p3_lift in Hb. rewrite E in Hb. exact (proj2 REL a b E Hb). }
    assert (ROsh : OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.MemNorm.ro_same rsegs m (p3_lift m msh0)).
    { intros a E. unfold p3_lift. rewrite E. reflexivity. }
    assert (RO2 : OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.MemNorm.ro_same rsegs (p3_lift m msh0) ms).
    { intros a E. rewrite (RS a E). unfold p3_lift. rewrite E. reflexivity. }
    exists R, (p3_lift m msh0), ms. split; [reflexivity|].
    split; [exact P2|]. split; [exact P3|]. split; [exact P4|]. split; [exact P8|].
    split; [exact P9|]. split; [exact P19|]. split; [exact P26|]. split; [exact P22|]. split; [exact P25|].
    split;
      [exact (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.MemNorm.munch_rel rsegs _ m _ _ msh0 REL RELsh ROsh
                MU1)|].
    split;
      [exact (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.MemNorm.wmono_rel rsegs m _ _ msh0 REL RELsh ROsh
                WM1)|].
    split; [exact (p3_rw_back _ msh0 (S + 336) _ RELsh ltac:(lia) RWS1)|].
    split;
      [exact (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.MemNorm.munch_rel rsegs _ _ msh0 ms m0' RELsh Hmem RO2
                MU2)|].
    split;
      [exact (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.MemNorm.wmono_rel rsegs _ msh0 ms m0' RELsh Hmem RO2
                WM2)|].
    split; [exact (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.MemNorm.ro_agree_same rsegs m ms HRO RS)|].
    split; [exact (p3_stk_back ms m0' lo spv Hmem ltac:(lia) ltac:(lia) ST2)|].
    split; [exact (p3_rw_back ms m0' fb _ Hmem ltac:(lia) RWF2) |].
    exact (p3_rw_back ms m0' id _ Hmem ltac:(lia) RW2).
Qed.

(* The shadow bytes p3_evt_ro needs: p3_evt's, on the normalized memory (normalize keeps every shadow byte). *)
Definition p3_evt_ro_shadow_R (id fb : Z) : Z -> Prop := fun a => p3_evt_shadow_R id fb a.

(* p3_evt_ro with the region premise (route (C); p3_evt_ro stays as it is, the 09:58Z ruling). *)
Lemma p3_evt_ro_on : asan_memset_contract_on -> reac_identity_init_contract_on ->
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (spv S id lo A fb : Z)
         (b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 b16 b17 b18 b19 b20 b21 b22 b23 b24 b25 b26 b27
          b28 : byte) (idb fbj : list byte),
    sp = Z_to_bv 64 spv -> s3 = Z_to_bv 64 S -> s11 = Z_to_bv 64 id -> s1 = Z_to_bv 64 A ->
    0 <= spv < 2 ^ 64 -> LOWMEM_END <= S -> S + 365 <= HIGHMEM_BEG ->
    0x5fe000 <= id -> id + 38 <= 2 ^ 64 -> id mod 2 = 0 ->
    (id + 38 <= S + 336 \/ S + 365 <= id) ->
    0x5fe000 <= A -> A + 40 <= 2 ^ 64 -> (A + 40 <= S + 336 \/ S + 365 <= A + 32) ->
    0x5fe000 <= fb -> fb + 35 <= 2 ^ 64 -> (fb + 35 <= S + 336 \/ S + 365 <= fb) ->
    (fb + 35 <= id \/ id + 38 <= fb) ->
    rw_cells rsegs m (S + 336) [C1 b0; C1 b1; C1 b2; C1 b3; C1 b4; C1 b5; C1 b6; C1 b7; C1 b8; C1 b9;
                                C1 b10; C1 b11; C1 b12; C1 b13; C1 b14; C1 b15; C1 b16; C1 b17; C1 b18; C1 b19;
                                C1 b20; C1 b21; C1 b22; C1 b23; C1 b24; C1 b25; C1 b26; C1 b27; C1 b28] ->
    rw_cells rsegs m id [CB 38 idb] ->
    rw_cells rsegs m (A + 32) [C8 (Z_to_bv 64 fb)] ->
    rw_cells rsegs m fb [CB 35 fbj] ->
    (forall m', bytes_at rsegs m' (S + 336) [Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 6] ->
       addressable m' id 38) ->
    (forall m', bytes_at rsegs m' (S + 360) [Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 3] ->
       addressable m' fb 35) ->
    end_in_app id 38 -> (id + 38 <= RT_LO \/ RT_HI <= id) ->
    (id + 38 <= spv - REAC_IDENTITY_INIT_K \/ spv <= id) ->
    end_in_app fb 35 -> app_mem (fb + 7) -> (fb + 35 <= RT_LO \/ RT_HI <= fb) ->
    (fb + 35 <= spv - REAC_IDENTITY_INIT_K \/ spv <= fb) ->
    stk rsegs m lo spv -> lo + REAC_IDENTITY_INIT_K <= spv -> HIGHMEM_BEG <= lo -> spv <= APPMEM_END ->
    asan_cells m -> A.ShadowRwOn.shadow_rw_on (p3_evt_ro_shadow_R id fb) m ->
      OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.MemNorm.ro_agree rsegs m ->
    evt rsegs
      (fun ms' => exists (R : bvmap 5 word) (msh m' : word -> option byte),
         ms' = MS R F (Z_to_bv 64 0x81b80) fc None m' (seg_rom rsegs) /\
         getr R 2 = sp /\ getr R 3 = gp /\ getr R 4 = tp /\ getr R 8 = s0 /\ getr R 9 = s1 /\
         getr R 19 = s3 /\ getr R 26 = s10 /\ getr R 22 = s6 /\ getr R 25 = s9 /\
         munch [(S + 336, S + 365)] m msh /\ wmono rsegs m msh /\
         rw_cells rsegs msh (S + 336) (p3_shc b5 b6 b7 b8 b9 b19 b20 b21 b22 b23) /\
         munch [(fb, fb + 35); (spv - REAC_IDENTITY_INIT_K, spv); (id, id + 38)] msh m' /\ wmono rsegs msh m' /\
         OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.MemNorm.ro_agree rsegs m' /\ stk rsegs m' lo spv /\
         rw_cells rsegs m' fb [CB 35 (repeat (Z_to_bv 8 0) 35)] /\
         rw_cells rsegs m' id [CB 38 (repeat (Z_to_bv 8 0) 38)])
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x81b14) fc None m (seg_rom rsegs)).
Proof.
  intros MSET RII ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m spv S id lo A fb b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 b16 b17 b18 b19 b20 b21 b22 b23
    b24 b25 b26 b27 b28 idb fbj
    E2 E19 E27 E9 Hspv HSlo HSHI Hid0 Hid38 Hidm HSEPs HA0 HA40 HSEPa Hfb0 Hfb35 HSEPb HSEPfi
    RWS RWI RWA RWF HADDR HADDRf HEI HRTI HSTI HEF HF7 HRTF HSTF ST HLO HHM HAE HAC HSW HRO.
  assert (EL : LOWMEM_END = 2147450880) by reflexivity.
  assert (EH : HIGHMEM_BEG = 17594333495296) by reflexivity.
  assert (ERT : RT_HI = 0xa9578) by reflexivity.
  pose proof (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.MemNorm.mem_rel_normalize rsegs m HRO) as REL.
  eapply evt_mono.
  - eapply OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.MemNorm.evt_normalize; [vm_compute; reflexivity | exact HRO
    |].
    apply (p3_evt_on MSET RII ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4
             t5 t6 F fc (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.MemNorm.normalize rsegs m) spv S id lo A fb b0
               b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13
             b14 b15 b16 b17 b18 b19 b20 b21 b22 b23 b24 b25 b26 b27 b28 idb fbj E2 E19 E27 E9 Hspv ltac:(lia)
             ltac:(lia) ltac:(lia) HSHI ltac:(lia) Hid38 Hidm HSEPs ltac:(lia) HA40 HSEPa ltac:(lia) Hfb35 HSEPb
             HSEPfi
             (p3_rw_rel m _ (S + 336) _ REL ltac:(lia) RWS) (p3_rw_rel m _ id _ REL ltac:(lia) RWI)
             (p3_rw_rel m _ (A + 32) _ REL ltac:(lia) RWA) (p3_rw_rel m _ fb _ REL ltac:(lia) RWF)
             HADDR HADDRf HEI HRTI HSTI HEF HF7 HRTF HSTF
             (p3_stk_rel m _ lo spv REL ltac:(lia) ltac:(lia) ST) HLO HHM HAE (p3_cells_rel m _ REL HAC)
             (A.ShadowRwOnT.shadow_rw_on_rel _ m _ REL HSW)
               (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.MemNorm.mem_inv_normalize rsegs m)).
  - intros s (s0' & (R & msh0 & m0' & -> & P2 & P3 & P4 & P8 & P9 & P19 & P26 & P22 & P25 & MU1 & WM1 & RWS1 &
               MU2 & WM2 & _ & ST2 & _ & _ & RWF2 & RW2) & MR & RS).
    destruct MR as (HR & HF & Hpc & Hsvc & Hres & Hfc & Hrom & Hmem).
    destruct s as [Rs Fs pcs svcs rvs fcs ms ros].
    cbn in HR, HF, Hpc, Hsvc, Hres, Hfc, Hrom, Hmem, RS. subst Rs Fs pcs svcs rvs fcs ros.
    assert (RELsh : OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.MemNorm.mem_rel rsegs (p3_lift m msh0) msh0).
    { split.
      - intros a. unfold OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.MemNorm.normalize, p3_lift. destruct
        (LM.ro_addr rsegs a) eqn:E; [|reflexivity].
        rewrite (MU1 a).
        + unfold OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.MemNorm.normalize. rewrite E. reflexivity.
        + pose proof (Tac_b5.sl_ro_lo a E) as Ha. cbn [Frame.outside]. split; [lia | exact I].
      - intros a b E Hb. unfold p3_lift in Hb. rewrite E in Hb. exact (proj2 REL a b E Hb). }
    assert (ROsh : OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.MemNorm.ro_same rsegs m (p3_lift m msh0)).
    { intros a E. unfold p3_lift. rewrite E. reflexivity. }
    assert (RO2 : OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.MemNorm.ro_same rsegs (p3_lift m msh0) ms).
    { intros a E. rewrite (RS a E). unfold p3_lift. rewrite E. reflexivity. }
    exists R, (p3_lift m msh0), ms. split; [reflexivity|].
    split; [exact P2|]. split; [exact P3|]. split; [exact P4|]. split; [exact P8|].
    split; [exact P9|]. split; [exact P19|]. split; [exact P26|]. split; [exact P22|]. split; [exact P25|].
    split; [exact (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.MemNorm.munch_rel rsegs _ m _ _ msh0 REL RELsh ROsh
      MU1)|].
    split; [exact (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.MemNorm.wmono_rel rsegs m _ _ msh0 REL RELsh ROsh
      WM1)|].
    split; [exact (p3_rw_back _ msh0 (S + 336) _ RELsh ltac:(lia) RWS1)|].
    split; [exact (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.MemNorm.munch_rel rsegs _ _ msh0 ms m0' RELsh Hmem
      RO2 MU2)|].
    split; [exact (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.MemNorm.wmono_rel rsegs _ msh0 ms m0' RELsh Hmem RO2
      WM2)|].
    split; [exact (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.MemNorm.ro_agree_same rsegs m ms HRO RS)|].
    split; [exact (p3_stk_back ms m0' lo spv Hmem ltac:(lia) ltac:(lia) ST2)|].
    split; [exact (p3_rw_back ms m0' fb _ Hmem ltac:(lia) RWF2) |].
    exact (p3_rw_back ms m0' id _ Hmem ltac:(lia) RW2).
Qed.

(* ---- Small helpers of the wrapper. ---- *)

(* Two readings of s1, both in range, are equal. *)
Lemma p3_A0 : forall (regs : bvmap 5 word) A A0, getr regs 9 = Z_to_bv 64 A -> 0 <= A < 2 ^ 64 ->
  getr regs 9 = Z_to_bv 64 A0 -> 0 <= A0 < 2 ^ 64 -> A0 = A.
Proof.
  intros regs A A0 H1 HA H2 HA0. rewrite H1 in H2.
  apply (f_equal (@bv_unsigned 64)) in H2. rewrite !MState.unsigned_lit in H2 by lia. lia.
Qed.

(* The frame-shadow byte x is the shadow byte of the frame byte fr + 8 (x - S(fr)) (Seg/P1.v p1_sfr_shadow). *)
Lemma p3_sfr_shadow : forall fr x, x = shadow_addr (fr + 8 * (x - Sfr fr)).
Proof.
  intros fr x. unfold Sfr, shadow_addr.
  replace (fr + 8 * (x - (fr / 8 + ASAN_K))) with (fr + (x - (fr / 8 + ASAN_K)) * 8) by lia.
  rewrite Z.div_add by lia. lia.
Qed.

(* Every side-stack metadata cell lies in [FS, FS + 36864) (Seg/P1.v p1_fs_meta_range). *)
Lemma p3_fs_meta_range : forall FS q, fs_meta FS q -> FS <= q < FS + 36864.
Proof.
  intros FS q H. split; [|exact (fs_meta_below FS q H)].
  destruct H as [H | [H | [ [c [Hc Hr]] | [c [j [Hc [Hj Heq]]]] ]]].
  - lia.
  - lia.
  - unfold ACw.a_fs_hint in Hr. lia.
  - subst q. exact (proj1 (a_fs_flag_range FS c j Hc Hj)).
Qed.

(* The registered globals of frame_AG lie in [0x21140, 0x9f8e8) (v1.9 FrameAPI; v1.8 [0x21120, 0x9f828); Seg/P1.v
   p1_ag_range). *)
Lemma p3_ag_range : forall a, in_globals AFw.frame_AG a -> 0x21140 <= a < 0x9f8e8.
Proof.
  intros a (lo & len & Hin & Hr).
  assert (Hall : forallb (fun p => (0x21140 <=? fst p) && (fst p + snd p <=? 0x9f8e8)) AFw.frame_AG = true)
    by (vm_compute; reflexivity).
  rewrite forallb_forall in Hall. specialize (Hall (lo, len) Hin). cbn [fst snd] in Hall.
  apply andb_true_iff in Hall as [H1 H2]. apply Z.leb_le in H1. apply Z.leb_le in H2. lia.
Qed.

(* A byte inside a bytes_at range reads back. *)
Lemma p3_ba_rd : forall m a bs q, bytes_at rsegs m a bs -> a <= q < a + Z.of_nat (length bs) ->
  exists b, mrd rsegs m (wa q) = Some b.
Proof.
  intros m a bs q (H0 & H1 & H) Hq.
  assert (Hk : (Z.to_nat (q - a) < length bs)%nat) by lia.
  specialize (H _ Hk). rewrite Z2Nat.id in H by lia. replace (a + (q - a)) with q in H by lia.
  destruct (nth_error bs (Z.to_nat (q - a))) as [b|] eqn:E; [exists b; exact H|].
  apply nth_error_None in E. lia.
Qed.

(* x is in one interval or outside it; in one of four intervals or outside all four (v1.9: the shadow window, the
   callee window, the object at fr + 2688 and first.sroa.7 at fr + 2880). *)
Lemma p3_in1 : forall lo hi x, (lo <= x < hi) \/ Frame.outside [(lo, hi)] x.
Proof.
  intros lo hi x. cbn [Frame.outside].
  destruct (Z_lt_le_dec x lo); [right; split; [lia | exact I]|].
  destruct (Z_lt_le_dec x hi); [left; lia | right; split; [lia | exact I]].
Qed.

Lemma p3_in4 : forall a b c d e f g h x,
  (a <= x < b) \/ (c <= x < d) \/ (e <= x < f) \/ (g <= x < h) \/
  Frame.outside [(a, b); (c, d); (e, f); (g, h)] x.
Proof.
  intros a b c d e f g h x.
  destruct (p3_in1 a b x) as [H1|H1]; [left; exact H1|].
  destruct (p3_in1 c d x) as [H2|H2]; [right; left; exact H2|].
  destruct (p3_in1 e f x) as [H3|H3]; [right; right; left; exact H3|].
  destruct (p3_in1 g h x) as [H4|H4]; [right; right; right; left; exact H4|].
  right; right; right; right. cbn [Frame.outside] in *. tauto.
Qed.

(* A readable+writable window yields a cell block of junk bytes (Seg/P12.v p12_cells). *)
Lemma p3_cells : forall m lo hi a (n : nat),
  stk rsegs m lo hi -> lo <= a -> a + Z.of_nat n <= hi ->
  exists junk, rw_cells rsegs m a [CB n junk].
Proof.
  intros m lo hi a n HST Hlo Hhi.
  destruct (stk_split rsegs m lo a hi HST ltac:(lia)) as (_ & H1).
  destruct (stk_split rsegs m a (a + Z.of_nat n) hi H1 ltac:(lia)) as (H2 & _).
  destruct (stk_carve rsegs m a (a + Z.of_nat n) n H2 ltac:(lia)) as (_ & junk & HR).
  replace (a + Z.of_nat n - Z.of_nat n) with a in HR by lia.
  exists junk. exact HR.
Qed.

(* One readable+writable spill word as a one-cell block (Seg/P12.v p12_q64_rw1): v1.9 P3's NEW-only load
   0x81b6c ld a0,32(s1). *)
Lemma p3_q64_rw1 : forall m lo hi a v,
  stk rsegs m lo hi -> lo <= a -> a + 8 <= hi -> q64 m a v -> rw_cells rsegs m a [C8 (Z_to_bv 64 v)].
Proof.
  intros m lo hi a v HST Hlo Hhi Hq.
  pose proof HST as (Hlo0 & Hhi2 & HSw). unfold q64 in Hq.
  split.
  - split; [cbn [cells_wf cell_wf]; repeat split; try exact I|].
    cbn [cells_bytes cbytes]. rewrite app_nil_r. exact Hq.
  - split; [lia|]. split; [cbn [cells_size csize]; lia|].
    intros i Hi. assert (Hib : 0 <= i < 8) by (cbn [cells_size csize] in Hi; lia).
    destruct (HSw (a + i) ltac:(lia)) as (Hw & _). exact Hw.
Qed.

(* The write-set predicates come in two flavours (Tac_slot's LibFr / ULFr, the same fixpoints); unfold both. *)
Ltac p3_out := cbn [LibFr.outside ULFr.outside]; repeat split; try exact I; lia.
Ltac p3_dj := cbn [LibFr.disjoint_from ULFr.disjoint_from cells_size csize]; repeat split; try exact I; lia.

Section P3W.
Context {fx : FPState} {LS : lib_shape} {rc : RunCeil}.
Variable B : malloc_syms.
Variable APIf : forall rc : RunCeil, ACw.AsanAllocAPI ACw.ASYMS AsanRTInv.RT.
Context {SH : sink_head} {SK : sink_syms}.
Variables ra empty : Z.
Hypothesis FF : frame_facts B APIf LS SH SK ra empty.

Open Scope Z_scope.

(* The allocator laws this file takes apart, each destructured ONCE here (a Theorem Labs lane's rule, 2026-10-28: append-only
   at every nesting level; the next generation adds named sub-projections, and then only these four proofs move).
   Every site below uses these lemmas, never a law's inner list. *)
Lemma p3_laws_store : forall H mem mem' md,
  ACw.aa_AH ACw.ASYMS AsanRTInv.RT (APIf rc) H mem md ->
  (forall x, 0 <= x < 2 ^ 64 -> ~ ACw.a_store_ok H (ACw.aa_stklo ACw.ASYMS AsanRTInv.RT (APIf rc) mem md) x ->
     mem' (Z_to_bv 64 x) = mem (Z_to_bv 64 x)) ->
  (forall x, 0 <= x < 2 ^ 64 -> writable_at rsegs mem x -> writable_at rsegs mem' x) ->
  ACw.aa_AH ACw.ASYMS AsanRTInv.RT (APIf rc) H mem' md /\
  (forall a, ACw.aa_owned ACw.ASYMS AsanRTInv.RT (APIf rc) H mem' md a <->
             ACw.aa_owned ACw.ASYMS AsanRTInv.RT (APIf rc) H mem md a) /\
  ACw.aa_stklo ACw.ASYMS AsanRTInv.RT (APIf rc) mem' md = ACw.aa_stklo ACw.ASYMS AsanRTInv.RT (APIf rc) mem md /\
  ACw.aa_stkhi ACw.ASYMS AsanRTInv.RT (APIf rc) mem' md = ACw.aa_stkhi ACw.ASYMS AsanRTInv.RT (APIf rc) mem md.
Proof.
  intros H mem mem' md HAH Hmc Hw.
  destruct (ACw.a_laws_store _ _ _ _ _ (ACw.aa_laws ACw.ASYMS AsanRTInv.RT (APIf rc)) H mem mem' md HAH Hmc Hw)
    as (H1 & H2 & H3 & H4).
  exact (conj H1 (conj H2 (conj H3 H4))).
Qed.

Lemma p3_laws_fs_place : forall H mem md FS,
  ACw.aa_AH ACw.ASYMS AsanRTInv.RT (APIf rc) H mem md ->
  word_mem rsegs mem (ACw.as_tp ACw.ASYMS) FS -> 0 <= FS < 2 ^ 64 ->
  ACw.GT <= FS /\ FS + ACw.FS_SIZE <= ACw.aa_stklo ACw.ASYMS AsanRTInv.RT (APIf rc) mem md /\
  (forall a, FS <= a < FS + ACw.FS_SIZE -> app_mem a).
Proof.
  intros H mem md FS HAH Hw Hr.
  destruct (ACw.a_laws_fs_place _ _ _ _ _ (ACw.aa_laws ACw.ASYMS AsanRTInv.RT (APIf rc)) H mem md FS HAH Hw Hr)
    as (H1 & H2 & _ & H4).
  exact (conj H1 (conj H2 H4)).
Qed.

Lemma p3_laws_fs_ok : forall H mem md FS,
  ACw.aa_AH ACw.ASYMS AsanRTInv.RT (APIf rc) H mem md ->
  word_mem rsegs mem (ACw.as_tp ACw.ASYMS) FS -> 0 <= FS < 2 ^ 64 -> ACw.a_fs_ok mem FS.
Proof.
  intros H mem md FS HAH Hw Hr.
  destruct (ACw.a_laws_fs_state _ _ _ _ _ (ACw.aa_laws ACw.ASYMS AsanRTInv.RT (APIf rc)) H mem md FS HAH Hw Hr)
    as (H1 & _).
  exact H1.
Qed.

Lemma p3_laws_fs_store : forall H mem mem' md FS,
  ACw.aa_AH ACw.ASYMS AsanRTInv.RT (APIf rc) H mem md ->
  word_mem rsegs mem (ACw.as_tp ACw.ASYMS) FS -> 0 <= FS < 2 ^ 64 ->
  (forall x, 0 <= x < 2 ^ 64 -> ~ ACw.a_store_ok H (ACw.aa_stklo ACw.ASYMS AsanRTInv.RT (APIf rc) mem md) x ->
     ~ (FS <= x < FS + ACw.FS_SIZE) -> ~ (exists b, FS <= b < FS + ACw.FS_SIZE /\ x = shadow_addr b) ->
     mem' (Z_to_bv 64 x) = mem (Z_to_bv 64 x)) ->
  (forall x, 0 <= x < 2 ^ 64 -> writable_at rsegs mem x -> writable_at rsegs mem' x) ->
  ACw.a_fs_ok mem' FS ->
  ACw.aa_AH ACw.ASYMS AsanRTInv.RT (APIf rc) H mem' md /\
  (forall a, ACw.aa_owned ACw.ASYMS AsanRTInv.RT (APIf rc) H mem' md a <->
             ACw.aa_owned ACw.ASYMS AsanRTInv.RT (APIf rc) H mem md a) /\
  ACw.aa_stklo ACw.ASYMS AsanRTInv.RT (APIf rc) mem' md = ACw.aa_stklo ACw.ASYMS AsanRTInv.RT (APIf rc) mem md /\
  ACw.aa_stkhi ACw.ASYMS AsanRTInv.RT (APIf rc) mem' md = ACw.aa_stkhi ACw.ASYMS AsanRTInv.RT (APIf rc) mem md.
Proof.
  intros H mem mem' md FS HAH Hw Hr Hmc Hwr Hok.
  destruct (ACw.a_laws_fs_store _ _ _ _ _ (ACw.aa_laws ACw.ASYMS AsanRTInv.RT (APIf rc)) H mem mem' md FS HAH Hw Hr
              Hmc Hwr Hok) as (H1 & H2 & H3 & H4).
  exact (conj H1 (conj H2 (conj H3 H4))).
Qed.

Lemma seg_P3 : asan_memset_contract -> reac_identity_init_contract ->
  Hcut B APIf ra (Inv_A81b80 B APIf ra) -> Hcut B APIf ra (Inv_A81b14 B APIf ra).
Proof.
  pose proof FRAME_BYTES_val as HFBv. pose proof FRAME_SHADOW_val as HFSv.
  intros MSET RII Hexit g c HInv.
  pose proof (proj1 FF) as SEGS.
  destruct HInv as (regs & mem & md & fr & Ec & HFRA & HENT & Hgn & HOUR & HCUR & HPRO & (A1 & HA1 & Q144) &
    (spv & A & idb & junk & Hr2 & Hr9 & Hr27 & HAb & Hspvb & RW192 & RWid & RWd & Q280 & Q240 &
     (jy & junk2 & RWjy & RWj2))).
  subst c.
  (* PRO's v1.9 position 16: [A + 32] = fr + 2880 (A4's 0x813cc), which 0x81b6c loads *)
  pose proof HPRO as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hsp32).
  pose proof (fra_app B APIf ra g fr [] regs mem md HFRA) as (HGT & Happ).
  pose proof (fra_frame B APIf ra g fr [] regs mem md HFRA) as (HFpl & _ & _ & _).
  pose proof (fra_win B APIf ra g fr [] regs mem md HFRA) as (Hwlo & Hwstk).
  pose proof (fra_stk B APIf ra g fr [] regs mem md HFRA) as Hstkfr.
  pose proof HFRA as HFRA2.
  destruct HFRA2 as (Afr & spf & s5 & HRT & HAH & Hro & Hsn & Hhalt & Hgimg & Hr2f & Hspm & Haspz &
    Hstklo & Hr4 & Hr8 & Hr9f & Hr3 & Hr19 & Hr26 & Hfrm & Hs5 & HAm & HAS & Hspa & Hfa & HA416 & HS4 & HAPP &
    Hspill & Hsel & Hfr24 & Hloc & Hhdr1 & Hhdr2 &
    Hsh & Hwin & Hsaved & Herrno & HAG & HWA & HSHI1 & HSHI2 & HSHI3 & Hhb & Hlive).
  pose proof (ACw.aa_laws ACw.ASYMS AsanRTInv.RT (APIf rc)) as ALAWS.
  unfold rg in Hr19, Hr27, Hr9f.
  (* the numeric layout constants, for lia *)
  assert (EK1 : REAC_IDENTITY_INIT_K = 2224) by reflexivity.
  assert (EK2 : ASAN_MEMSET_K = 2208) by reflexivity.
  assert (EK3 : AFw.SLOT_STACK = 1048576) by reflexivity.
  assert (EKF : FN_STACK = 1044480) by reflexivity.
  assert (EK4 : HIGHMEM_BEG = 17594333495296) by reflexivity.
  assert (EK5 : APPMEM_END = 140737488355328) by reflexivity.
  assert (EK6 : LOWMEM_END = 2147450880) by reflexivity.
  assert (EK7 : RT_HI = 0xa9578) by reflexivity.
  assert (EK8 : RT_LO = 0x9fad0) by reflexivity.
  assert (EK9 : ACw.GT = 6283264) by reflexivity.
  (* sp = spv, s1 = A *)
  assert (Espf : spv = spf).
  { pose proof Haspz as Ha. unfold ACw.aspZ in Ha. rewrite Hr2 in Ha.
    rewrite MState.unsigned_lit in Ha by lia. exact Ha. }
  destruct Espf.
  assert (HAfr : Afr + 312 <= 2 ^ 64).
  { pose proof Hspill as Hq. unfold q64 in Hq. apply bytes_at_bound in Hq. rewrite length_le8 in Hq. lia. }
  assert (Hstkhigh : HIGHMEM_BEG <= ACw.aa_stklo ACw.ASYMS AsanRTInv.RT (APIf rc) mem md)
    by (apply (ACw.a_laws_stack_high _ _ _ _ _ ALAWS ([] ++ g_H g) mem md HAH)).
  assert (EA : Afr = A).
  { rewrite Hr9 in Hr9f. apply (f_equal (@bv_unsigned 64)) in Hr9f.
    rewrite !MState.unsigned_lit in Hr9f by lia. lia. }
  subst Afr.
  rewrite Haspz in Hwlo, Hwstk.
  assert (HspE : spv <= APPMEM_END) by lia.
  assert (Hlo : HIGHMEM_BEG <= spv - FN_STACK) by lia.
  (* the frame is apart from the callee windows (fra_frame, K = 2224 and K = 2208) *)
  assert (HSEPf : fr + FRAME_BYTES <= spv - REAC_IDENTITY_INIT_K \/ spv <= fr).
  { rewrite <- Haspz. apply HFpl. lia. }
  assert (HSEPm : fr + FRAME_BYTES <= spv - ASAN_MEMSET_K \/ spv <= fr).
  { rewrite <- Haspz. apply HFpl. lia. }
  (* the frame and its shadow *)
  assert (Hfr0 : 0 <= fr) by (pose proof (Happ fr ltac:(lia)) as H; unfold app_mem in H; lia).
  assert (Hfrhi : fr + FRAME_BYTES <= APPMEM_END)
    by (pose proof (Happ (fr + FRAME_BYTES - 1) ltac:(lia)) as H; unfold app_mem in H; lia).
  assert (Hfr8 : fr mod 8 = 0) by (pose proof Hfrm as Hfrm0; Z.div_mod_to_equations; lia).
  assert (Hinsh : forall k, 0 <= k < FRAME_SHADOW -> in_shadow (Sfr fr + k)).
  { intros k Hk. replace (Sfr fr + k) with (shadow_addr (fr + 8 * k)).
    - apply shadow_of_app. apply Happ. lia.
    - unfold Sfr, shadow_addr. clear -Hk. Z.div_mod_to_equations. lia. }
  assert (HSlo : LOWMEM_END <= Sfr fr).
  { pose proof (Hinsh 0 ltac:(lia)) as H. unfold in_shadow, LOWSHADOW_END, HIGHSHADOW_BEG in H. lia. }
  assert (HShi : Sfr fr + FRAME_SHADOW <= HIGHMEM_BEG).
  { pose proof (Hinsh (FRAME_SHADOW - 1) ltac:(lia)) as H. unfold in_shadow, LOWSHADOW_END, HIGHSHADOW_BEG in H. lia. }
  assert (HSdisj : Sfr fr + FRAME_SHADOW <= fr \/ fr + FRAME_BYTES <= Sfr fr).
  { pose proof (Happ fr ltac:(lia)) as H1. pose proof (Happ (fr + FRAME_BYTES - 1) ltac:(lia)) as H2.
    unfold app_mem in H1, H2. lia. }
  assert (Eshad : forall k, shadow_addr (fr + 8 * k) = Sfr fr + k).
  { intros k. unfold Sfr, shadow_addr. clear. Z.div_mod_to_equations. lia. }
  (* the 392 shadow bytes, split at 336 and 365 *)
  destruct Hsh as (sh & Hshb & Hshl0).
  assert (Hshl : length sh = 392%nat) by (rewrite Hshl0; reflexivity).
  assert (Esh : sh = firstn 336 sh ++ firstn 29 (skipn 336 sh) ++ skipn 365 sh).
  { symmetry. apply (CB3_bytes 336 29 sh). lia. }
  assert (Hl1 : length (firstn 336 sh) = 336%nat) by (rewrite length_firstn, Hshl; reflexivity).
  assert (Hl3 : length (skipn 365 sh) = 27%nat) by (rewrite length_skipn, Hshl; reflexivity).
  rewrite Esh in Hshb. apply bytes_at_app in Hshb. destruct Hshb as [Hsh1 Hshb].
  apply bytes_at_app in Hshb. destruct Hshb as [Hsh2 Hsh3].
  rewrite Hl1 in Hsh2, Hsh3.
  assert (Hl2 : length (firstn 29 (skipn 336 sh)) = 29%nat) by (rewrite length_firstn, length_skipn, Hshl; reflexivity).
  rewrite Hl2 in Hsh3.
  replace (Sfr fr + Z.of_nat 336 + Z.of_nat 29) with (Sfr fr + 365) in Hsh3 by lia.
  replace (Sfr fr + Z.of_nat 336) with (Sfr fr + 336) in Hsh2 by lia.
  remember (firstn 29 (skipn 336 sh)) as sh2 eqn:Esh2.
  destruct sh2 as [|b0 [|b1 [|b2 [|b3 [|b4 [|b5 [|b6 [|b7 [|b8 [|b9 [|b10 [|b11 [|b12 [|b13 [|b14 [|b15 [|b16
    [|b17 [|b18 [|b19 [|b20 [|b21 [|b22 [|b23 [|b24 [|b25 [|b26 [|b27 [|b28 [|bx shx]]]]]]]]]]]]]]]]]]]]]]]]]]]]]];
    try (cbn in Hl2; lia).
  pose proof (AsanRTInv.RT_shadow_rw _ _ _ HRT) as HSW.
  pose proof (AsanRTInv.RT_cells _ _ _ HRT) as HACm.
  assert (RWS : rw_cells rsegs mem (Sfr fr + 336)
                  [C1 b0; C1 b1; C1 b2; C1 b3; C1 b4; C1 b5; C1 b6; C1 b7; C1 b8; C1 b9;
                   C1 b10; C1 b11; C1 b12; C1 b13; C1 b14; C1 b15; C1 b16; C1 b17; C1 b18; C1 b19;
                   C1 b20; C1 b21; C1 b22; C1 b23; C1 b24; C1 b25; C1 b26; C1 b27; C1 b28]).
  { split.
    - split; [cbn; tauto|]. exact Hsh2.
    - split; [lia|]. split; [cbn [cells_size csize]; lia|]. intros i Hi. cbn [cells_size csize] in Hi.
      replace (Sfr fr + 336 + i) with (Sfr fr + (336 + i)) by lia.
      exact (proj1 (HSW _ (Hinsh (336 + i) ltac:(lia)))). }
  (* the object at fr + 2688 is addressable once its 5 shadow bytes read 0,0,0,0,6 *)
  assert (HADDR : forall m', bytes_at rsegs m' (Sfr fr + 336)
                    [Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 6] ->
                  addressable m' (fr + 2688) 38).
  { intros m' HB.
    assert (HB' : bytes_at rsegs m' (Sfr fr + 336) (repeat (Z_to_bv 8 0) (Z.to_nat 4) ++ [Z_to_bv 8 6]))
      by exact HB.
    apply bytes_at_app in HB'. destruct HB' as [HB1 HB2].
    change (Z.of_nat (length (repeat (Z_to_bv 8 0) (Z.to_nat 4)))) with 4 in HB2.
    replace 38 with (8 * 4 + 6) by reflexivity.
    apply p3_addr_cat.
    - apply p3_addr_zero; [| lia | lia | lia | intros i Hi; apply Happ; lia |].
      + clear -Hfr8. Z.div_mod_to_equations. lia.
      + replace (fr + 2688) with (fr + 8 * 336) by lia. rewrite Eshad. exact HB1.
    - replace (fr + 2688 + 8 * 4) with (fr + 8 * 340) by lia.
      apply p3_addr_part; [| lia | vm_compute; reflexivity | lia | lia | intros i Hi; apply Happ; lia |].
      + clear -Hfr8. Z.div_mod_to_equations. lia.
      + rewrite Eshad. replace (Sfr fr + 340) with (Sfr fr + 336 + 4) by lia. exact HB2. }
  (* first.sroa.7's 35 bytes at fr + 2880 are addressable once their 5 shadow bytes read 0,0,0,0,3 *)
  assert (HADDRf : forall m', bytes_at rsegs m' (Sfr fr + 360)
                     [Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 3] ->
                   addressable m' (fr + 2880) 35).
  { intros m' HB.
    assert (HB' : bytes_at rsegs m' (Sfr fr + 360) (repeat (Z_to_bv 8 0) (Z.to_nat 4) ++ [Z_to_bv 8 3]))
      by exact HB.
    apply bytes_at_app in HB'. destruct HB' as [HB1 HB2].
    change (Z.of_nat (length (repeat (Z_to_bv 8 0) (Z.to_nat 4)))) with 4 in HB2.
    replace 35 with (8 * 4 + 3) by reflexivity.
    apply p3_addr_cat.
    - apply p3_addr_zero; [| lia | lia | lia | intros i Hi; apply Happ; lia |].
      + clear -Hfr8. Z.div_mod_to_equations. lia.
      + replace (fr + 2880) with (fr + 8 * 360) by lia. rewrite Eshad. exact HB1.
    - replace (fr + 2880 + 8 * 4) with (fr + 8 * 364) by lia.
      apply p3_addr_part; [| lia | vm_compute; reflexivity | lia | lia | intros i Hi; apply Happ; lia |].
      + clear -Hfr8. Z.div_mod_to_equations. lia.
      + rewrite Eshad. replace (Sfr fr + 364) with (Sfr fr + 360 + 4) by lia. exact HB2. }
  assert (Hidm : (fr + 2688) mod 2 = 0) by (clear -Hfrm; Z.div_mod_to_equations; lia).
  assert (HEI : end_in_app (fr + 2688) 38) by (right; apply Happ; lia).
  assert (HEF : end_in_app (fr + 2880) 35) by (right; apply Happ; lia).
  assert (HF7 : app_mem (fr + 2880 + 7)) by (apply Happ; lia).
  (* the 35 frame bytes the memset writes, and the pointer spill [A + 32] it reads them through *)
  destruct (p3_cells mem fr (fr + FRAME_BYTES) (fr + 2880) 35 Hstkfr ltac:(lia) ltac:(cbn [Z.of_nat]; lia))
    as (fbj & RWF).
  assert (Q32 : q64 mem (A + 32) (fr + 2880)).
  { destruct Hsp32 as (A2 & HA2 & Hq).
    assert (EA2 : A2 = A).
    { unfold rg in HA2. pose proof Hq as Hqb. unfold q64 in Hqb. apply bytes_at_bound in Hqb.
      rewrite length_le8 in Hqb. rewrite Hr9 in HA2. apply (f_equal (@bv_unsigned 64)) in HA2.
      rewrite !Z_to_bv_unsigned in HA2. unfold bv_wrap, bv_modulus in HA2.
      change (2 ^ Z.of_N 64)%Z with (2 ^ 64)%Z in HA2.
      clear - HA2 Hqb HAS HAPP HAb EK5. revert HA2 Hqb. Z.div_mod_to_equations. lia. }
    subst A2. exact Hq. }
  assert (RWA : rw_cells rsegs mem (A + 32) [C8 (Z_to_bv 64 (fr + 2880))]).
  { apply (p3_q64_rw1 mem (g_S g - AFw.SLOT_STACK) (g_S g) (A + 32) (fr + 2880) Hwin); [lia | lia | exact Q32]. }
  rewrite SEGS.
  eapply (p3_run regs (Z_to_bv 64 0x81b14) mem md
    (fun R pc' mem' => pc' = Z_to_bv 64 0x81b80 /\
       getr R 2 = getr regs 2 /\ getr R 3 = getr regs 3 /\ getr R 4 = getr regs 4 /\ getr R 8 = getr regs 8 /\
       getr R 9 = getr regs 9 /\ getr R 19 = getr regs 19 /\ getr R 26 = getr regs 26 /\
       getr R 22 = getr regs 22 /\ getr R 25 = getr regs 25 /\
       exists msh, Frame.munch [(Sfr fr + 336, Sfr fr + 365)] mem msh /\ Frame.wmono rsegs mem msh /\
         rw_cells rsegs msh (Sfr fr + 336) (p3_shc b5 b6 b7 b8 b9 b19 b20 b21 b22 b23) /\
         Frame.munch [(fr + 2880, fr + 2880 + 35); (spv - REAC_IDENTITY_INIT_K, spv);
                      (fr + 2688, fr + 2688 + 38)] msh mem' /\
         Frame.wmono rsegs msh mem' /\
         OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.MemNorm.ro_agree rsegs mem' /\
         stk rsegs mem' (spv - FN_STACK) spv /\
         rw_cells rsegs mem' (fr + 2880) [CB 35 (repeat (Z_to_bv 8 0) 35)] /\
         rw_cells rsegs mem' (fr + 2688) [CB 38 (repeat (Z_to_bv 8 0) 38)])
    (Post B APIf ra g)).
  - exact Hhalt.
  - unfold RegisterBridge.canonical_register_state; cbn [Regs6ss.mkR_of YK11.mkst].
    eapply evt_mono.
    + apply (p3_evt_ro MSET RII) with (spv := spv) (S := Sfr fr) (id := fr + 2688) (lo := spv - FN_STACK)
        (A := A) (fb := fr + 2880)
        (b0 := b0) (b1 := b1) (b2 := b2) (b3 := b3) (b4 := b4) (b5 := b5) (b6 := b6) (b7 := b7) (b8 := b8)
        (b9 := b9) (b10 := b10) (b11 := b11) (b12 := b12) (b13 := b13) (b14 := b14) (b15 := b15) (b16 := b16)
        (b17 := b17) (b18 := b18) (b19 := b19) (b20 := b20) (b21 := b21) (b22 := b22) (b23 := b23) (b24 := b24)
        (b25 := b25) (b26 := b26) (b27 := b27) (b28 := b28) (idb := idb) (fbj := fbj).
      (* the separation side conditions (A + 32 / fb = fr + 2880 against S(fr) + 336 .. 364, fb against the window
         and the object) follow from FRA's facts *)
      all: try assumption.
      all: lia.
    + intros ms' (R & msh & m' & Hms & P2 & P3 & P4 & P8 & P9 & P19 & P26 & P22 & P25 & MU1 & WM1 & RWS1 &
                  MU2 & WM2 & RO2 & ST2 & RWF2 & RW2).
      exists R, (Z_to_bv 64 0x81b80), m'. split; [exact Hms|].
      split; [reflexivity|]. split; [exact P2|]. split; [exact P3|]. split; [exact P4|]. split; [exact P8|].
      split; [exact P9|]. split; [exact P19|]. split; [exact P26|]. split; [exact P22|]. split; [exact P25|].
      exists msh. split; [exact MU1|]. split; [exact WM1|]. split; [exact RWS1|].
      split; [exact MU2|]. split; [exact WM2|]. split; [exact RO2|]. split; [exact ST2|].
      split; [exact RWF2 | exact RW2].
  - intros R pc' mem' regs'' md'
      (Hpc & K2 & K3 & K4 & K8 & K9 & K19 & K26 & K22 & K25 & msh & MU1 & WM1 & RWS1 & MU2 & WM2 & RO2 & ST2
       & RWF2 & RW2)
      Hreg Hmat.
    subst pc'.
    assert (E2 : getr regs'' 2 = getr regs 2) by (rewrite Hreg; exact K2).
    assert (E3 : getr regs'' 3 = getr regs 3) by (rewrite Hreg; exact K3).
    assert (E4 : getr regs'' 4 = getr regs 4) by (rewrite Hreg; exact K4).
    assert (E8 : getr regs'' 8 = getr regs 8) by (rewrite Hreg; exact K8).
    assert (E9 : getr regs'' 9 = getr regs 9) by (rewrite Hreg; exact K9).
    assert (E19 : getr regs'' 19 = getr regs 19) by (rewrite Hreg; exact K19).
    assert (E26 : getr regs'' 26 = getr regs 26) by (rewrite Hreg; exact K26).
    assert (E22 : getr regs'' 22 = getr regs 22) by (rewrite Hreg; exact K22).
    assert (E25 : getr regs'' 25 = getr regs 25) by (rewrite Hreg; exact K25).
    (* the shadow bytes after the stores *)
    assert (HB29 : bytes_at rsegs msh (Sfr fr + 336) (cells_bytes (p3_shc b5 b6 b7 b8 b9 b19 b20 b21 b22 b23))).
    { destruct RWS1 as [[_ HB] _]. exact HB. }
    assert (HL29 : Z.of_nat (length (cells_bytes (p3_shc b5 b6 b7 b8 b9 b19 b20 b21 b22 b23))) = 29)
      by reflexivity.
    (* the whole write set of the run: the 29 shadow bytes, the callee windows, the 38 object bytes and the 35
       bytes of first.sroa.7 *)
    assert (MUs : Frame.munch [(Sfr fr + 336, Sfr fr + 365); (spv - REAC_IDENTITY_INIT_K, spv);
                               (fr + 2688, fr + 2688 + 38); (fr + 2880, fr + 2880 + 35)] mem msh).
    { eapply Frame.munch_weaken; [| exact MU1]. intros x Hx. cbn [Frame.outside] in *. tauto. }
    assert (MUall : Frame.munch [(Sfr fr + 336, Sfr fr + 365); (spv - REAC_IDENTITY_INIT_K, spv);
                                 (fr + 2688, fr + 2688 + 38); (fr + 2880, fr + 2880 + 35)] mem mem').
    { apply (Frame.munch_trans _ mem msh mem' MUs).
      eapply Frame.munch_weaken; [| exact MU2]. intros x Hx. cbn [Frame.outside] in *. tauto. }
    assert (WMall : Frame.wmono rsegs mem mem') by (eapply Frame.wmono_trans; [exact WM1 | exact WM2]).
    assert (Hwrit1 : forall x, 0 <= x < 2 ^ 64 -> writable_at rsegs mem x -> writable_at rsegs msh x)
      by (intros x _ Hwx; exact (WM1 (Z_to_bv 64 x) Hwx)).
    assert (Hwrit2 : forall x, 0 <= x < 2 ^ 64 -> writable_at rsegs mem x -> writable_at rsegs mem' x)
      by (intros x _ Hwx; exact (WMall (Z_to_bv 64 x) Hwx)).
    (* AH and the stack bounds after the stores (msh) and after the calls (mem'), by frame arm *)
    assert (AHSTK : ACw.aa_AH ACw.ASYMS AsanRTInv.RT (APIf rc) ([] ++ g_H g) msh md /\
                    ACw.aa_stklo ACw.ASYMS AsanRTInv.RT (APIf rc) msh md
                      = ACw.aa_stklo ACw.ASYMS AsanRTInv.RT (APIf rc) mem md /\
                    ACw.aa_AH ACw.ASYMS AsanRTInv.RT (APIf rc) ([] ++ g_H g) mem' md /\
                    (forall a, ACw.aa_owned ACw.ASYMS AsanRTInv.RT (APIf rc) ([] ++ g_H g) mem' md a <->
                               ACw.aa_owned ACw.ASYMS AsanRTInv.RT (APIf rc) ([] ++ g_H g) mem md a) /\
                    ACw.aa_stklo ACw.ASYMS AsanRTInv.RT (APIf rc) mem' md
                      = ACw.aa_stklo ACw.ASYMS AsanRTInv.RT (APIf rc) mem md /\
                    ACw.aa_stkhi ACw.ASYMS AsanRTInv.RT (APIf rc) mem' md
                      = ACw.aa_stkhi ACw.ASYMS AsanRTInv.RT (APIf rc) mem md).
    { destruct Hloc as [[Hs50 [Hspfr Hreal]]|[Hs5fr [Hfsb [Hfs Hrec]]]].
      - (* real arm: a_laws_store; the shadow bytes are the shadow of frame bytes, the window, the object and
           first.sroa.7 are at or above stklo *)
        assert (Hmc1 : forall x, 0 <= x < 2 ^ 64 ->
                  ~ ACw.a_store_ok ([] ++ g_H g) (ACw.aa_stklo ACw.ASYMS AsanRTInv.RT (APIf rc) mem md) x ->
                  msh (Z_to_bv 64 x) = mem (Z_to_bv 64 x)).
        { intros x Hx Hnok.
          destruct (p3_in1 (Sfr fr + 336) (Sfr fr + 365) x) as [Hin|Hout].
          - exfalso. apply Hnok. right. right. right. exists (fr + 8 * (x - Sfr fr)).
            split; [exact (p3_sfr_shadow fr x)|]. right. left.
            specialize (Hreal (fr + 8 * (x - Sfr fr)) ltac:(lia)). lia.
          - apply MU1. rewrite MState.unsigned_lit by exact Hx. exact Hout. }
        destruct (p3_laws_store ([] ++ g_H g) mem msh md HAH Hmc1 Hwrit1) as (HAHs & _ & HSTKs & _).
        assert (Hmc2 : forall x, 0 <= x < 2 ^ 64 ->
                  ~ ACw.a_store_ok ([] ++ g_H g) (ACw.aa_stklo ACw.ASYMS AsanRTInv.RT (APIf rc) mem md) x ->
                  mem' (Z_to_bv 64 x) = mem (Z_to_bv 64 x)).
        { intros x Hx Hnok.
          destruct (p3_in4 (Sfr fr + 336) (Sfr fr + 365) (spv - REAC_IDENTITY_INIT_K) spv
                      (fr + 2688) (fr + 2688 + 38) (fr + 2880) (fr + 2880 + 35) x)
            as [Hin|[Hin|[Hin|[Hin|Hout]]]].
          - exfalso. apply Hnok. right. right. right. exists (fr + 8 * (x - Sfr fr)).
            split; [exact (p3_sfr_shadow fr x)|]. right. left.
            specialize (Hreal (fr + 8 * (x - Sfr fr)) ltac:(lia)). lia.
          - exfalso. apply Hnok. right. left. lia.
          - exfalso. apply Hnok. right. left. specialize (Hreal x ltac:(lia)). lia.
          - exfalso. apply Hnok. right. left. specialize (Hreal x ltac:(lia)). lia.
          - apply MUall. rewrite MState.unsigned_lit by exact Hx. exact Hout. }
        destruct (p3_laws_store ([] ++ g_H g) mem mem' md HAH Hmc2 Hwrit2) as (HAH1 & Hown1 & HSTK1 & Hhi1).
        exact (conj HAHs (conj HSTKs (conj HAH1 (conj Hown1 (conj HSTK1 Hhi1))))).
      - (* side arm: a_laws_fs_store; the frame lies in the FakeStack FS (the word at tp), whose metadata is app
           memory below the frame and below stklo *)
        destruct (Hfs (fr + FRAME_BYTES - 1) ltac:(lia)) as (FS & HFSr & HFSw & _ & HFShi).
        pose proof (Hfsb FS HFSw HFSr) as HFSlo.
        destruct (p3_laws_fs_place ([] ++ g_H g) mem md FS HAH HFSw HFSr) as (HGTFS & HFSend & HFSapp).
        pose proof (p3_laws_fs_ok ([] ++ g_H g) mem md FS HAH HFSw HFSr) as Hfsok0.
        assert (HFSZ : ACw.FS_SIZE = 11571200) by reflexivity.
        (* every byte present in mem stays present in msh and in mem' *)
        assert (Hpres1 : forall q, 0 <= q < 2 ^ 64 -> (exists b, mbyte rsegs mem q = Some b) ->
                  exists b, mbyte rsegs msh q = Some b).
        { intros q Hq (b & Hb).
          destruct (p3_in1 (Sfr fr + 336) (Sfr fr + 365) q) as [Hin|Hout].
          - destruct (p3_ba_rd msh (Sfr fr + 336) _ q HB29 ltac:(rewrite HL29; lia)) as (b' & Hb').
            exists b'. unfold mbyte. unfold mrd, wa in Hb'. exact Hb'.
          - exists b. unfold mbyte in Hb |- *. rewrite MU1; [exact Hb|].
            rewrite MState.unsigned_lit by exact Hq. exact Hout. }
        assert (Hpres2 : forall q, 0 <= q < 2 ^ 64 -> (exists b, mbyte rsegs msh q = Some b) ->
                  exists b, mbyte rsegs mem' q = Some b).
        { intros q Hq (b & Hb).
          destruct (p3_in1 (spv - REAC_IDENTITY_INIT_K) spv q) as [Hin|Hout1].
          - destruct (rd_of_stk mem' (spv - FN_STACK) spv ST2 q ltac:(lia)) as (b' & Hb').
            exists b'. unfold mbyte. unfold mrd, wa in Hb'. exact Hb'.
          - destruct (p3_in1 (fr + 2688) (fr + 2688 + 38) q) as [Hin2|Hout2].
            + pose proof (stk_of_rw_cells rsegs mem' (fr + 2688) [CB 38 (repeat (Z_to_bv 8 0) 38)] RW2) as Hst.
              destruct (rd_of_stk mem' (fr + 2688) (fr + 2688 + 38) Hst q Hin2) as (b' & Hb').
              exists b'. unfold mbyte. unfold mrd, wa in Hb'. exact Hb'.
            + destruct (p3_in1 (fr + 2880) (fr + 2880 + 35) q) as [Hin3|Hout3].
              * pose proof (stk_of_rw_cells rsegs mem' (fr + 2880) [CB 35 (repeat (Z_to_bv 8 0) 35)] RWF2) as Hst.
                destruct (rd_of_stk mem' (fr + 2880) (fr + 2880 + 35) Hst q Hin3) as (b' & Hb').
                exists b'. unfold mbyte. unfold mrd, wa in Hb'. exact Hb'.
              * exists b. unfold mbyte in Hb |- *. rewrite MU2; [exact Hb|].
                rewrite MState.unsigned_lit by exact Hq.
                cbn [Frame.outside] in Hout1, Hout2, Hout3 |- *. tauto. }
        (* the FakeStack's metadata cells are app bytes below the frame and below the window *)
        assert (Hmeta1 : forall q, fs_meta FS q -> Frame.outside [(Sfr fr + 336, Sfr fr + 365)] q).
        { intros q Hq. pose proof (p3_fs_meta_range FS q Hq) as Hqr.
          assert (Hqa : app_mem q) by (apply HFSapp; lia). unfold app_mem in Hqa. p3_out. }
        assert (Hmeta2 : forall q, fs_meta FS q ->
                  Frame.outside [(Sfr fr + 336, Sfr fr + 365); (spv - REAC_IDENTITY_INIT_K, spv);
                                 (fr + 2688, fr + 2688 + 38); (fr + 2880, fr + 2880 + 35)] q).
        { intros q Hq. pose proof (p3_fs_meta_range FS q Hq) as Hqr.
          assert (Hqa : app_mem q) by (apply HFSapp; lia). unfold app_mem in Hqa. p3_out. }
        assert (Hfsok1 : ACw.a_fs_ok msh FS)
          by (apply (a_fs_ok_pres [(Sfr fr + 336, Sfr fr + 365)] mem msh FS Hfsok0 MU1 Hwrit1 Hpres1 Hmeta1); lia).
        assert (Hfsok2 : ACw.a_fs_ok mem' FS).
        { apply (a_fs_ok_pres [(Sfr fr + 336, Sfr fr + 365); (spv - REAC_IDENTITY_INIT_K, spv);
                               (fr + 2688, fr + 2688 + 38); (fr + 2880, fr + 2880 + 35)] mem mem' FS Hfsok0
                               MUall Hwrit2);
            [| exact Hmeta2 | lia | lia].
          intros q Hq Hp. exact (Hpres2 q Hq (Hpres1 q Hq Hp)). }
        assert (Hmc1 : forall x, 0 <= x < 2 ^ 64 ->
                  ~ ACw.a_store_ok ([] ++ g_H g) (ACw.aa_stklo ACw.ASYMS AsanRTInv.RT (APIf rc) mem md) x ->
                  ~ (FS <= x < FS + ACw.FS_SIZE) ->
                  ~ (exists b, FS <= b < FS + ACw.FS_SIZE /\ x = shadow_addr b) ->
                  msh (Z_to_bv 64 x) = mem (Z_to_bv 64 x)).
        { intros x Hx Hnok Hnfs Hnsh.
          destruct (p3_in1 (Sfr fr + 336) (Sfr fr + 365) x) as [Hin|Hout].
          - exfalso. apply Hnsh. exists (fr + 8 * (x - Sfr fr)). split; [lia | exact (p3_sfr_shadow fr x)].
          - apply MU1. rewrite MState.unsigned_lit by exact Hx. exact Hout. }
        destruct (p3_laws_fs_store ([] ++ g_H g) mem msh md FS HAH HFSw HFSr Hmc1 Hwrit1 Hfsok1)
          as (HAHs & _ & HSTKs & _).
        assert (Hmc2 : forall x, 0 <= x < 2 ^ 64 ->
                  ~ ACw.a_store_ok ([] ++ g_H g) (ACw.aa_stklo ACw.ASYMS AsanRTInv.RT (APIf rc) mem md) x ->
                  ~ (FS <= x < FS + ACw.FS_SIZE) ->
                  ~ (exists b, FS <= b < FS + ACw.FS_SIZE /\ x = shadow_addr b) ->
                  mem' (Z_to_bv 64 x) = mem (Z_to_bv 64 x)).
        { intros x Hx Hnok Hnfs Hnsh.
          destruct (p3_in4 (Sfr fr + 336) (Sfr fr + 365) (spv - REAC_IDENTITY_INIT_K) spv
                      (fr + 2688) (fr + 2688 + 38) (fr + 2880) (fr + 2880 + 35) x)
            as [Hin|[Hin|[Hin|[Hin|Hout]]]].
          - exfalso. apply Hnsh. exists (fr + 8 * (x - Sfr fr)). split; [lia | exact (p3_sfr_shadow fr x)].
          - exfalso. apply Hnok. right. left. lia.
          - exfalso. apply Hnfs. lia.
          - exfalso. apply Hnfs. lia.
          - apply MUall. rewrite MState.unsigned_lit by exact Hx. exact Hout. }
        destruct (p3_laws_fs_store ([] ++ g_H g) mem mem' md FS HAH HFSw HFSr Hmc2 Hwrit2 Hfsok2)
          as (HAH1 & Hown1 & HSTK1 & Hhi1).
        exact (conj HAHs (conj HSTKs (conj HAH1 (conj Hown1 (conj HSTK1 Hhi1))))). }
    destruct AHSTK as (HAHs & HSTKs & HAH1 & Hown1 & HSTK1 & Hhi1).
    (* FRA across the 19 shadow stores (sl_fr_meta) *)
    assert (HROs : OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.MemNorm.ro_agree rsegs msh).
    { apply (Tac_b5.sl_ro_keep [(Sfr fr + 336, Sfr fr + 365)] mem msh Hro MU1).
      intros x Hx. p3_out. }
    assert (HDJs : AsanRTInv.rt_disjoint [(Sfr fr + 336, Sfr fr + 365)]).
    { unfold AsanRTInv.rt_disjoint, RT_LO, RT_HI, RT_GOT_AF, RT_AF, RT_GOT_VERB, RT_VERB,
        RT_GOT_CF, RT_CF, RT_TSDI, RT_TSDK, RT_PGSZ, RT_TP, RT_TSDMAIN, RT_REAL_LO, RT_REAL_HI,
        RT_IMAP, RT_IMEM, RT_MUG, RT_AGLOB, RT_AGLOB_LEN. cbn [Frame.disjoint_from].
      repeat split; (lia || exact I). }
    assert (Hshs : exists sh', bytes_at rsegs msh (Sfr fr) sh' /\ length sh' = Z.to_nat FRAME_SHADOW).
    { exists (firstn 336 sh ++ cells_bytes (p3_shc b5 b6 b7 b8 b9 b19 b20 b21 b22 b23) ++ skipn 365 sh).
      split.
      - apply bytes_at_app. split.
        + apply (bytes_at_transport rsegs [(Sfr fr + 336, Sfr fr + 365)] mem msh (Sfr fr) _ Hsh1 MU1).
          rewrite Hl1. p3_dj.
        + rewrite Hl1. apply bytes_at_app. split.
          * replace (Sfr fr + Z.of_nat 336) with (Sfr fr + 336) by lia. exact HB29.
          * replace (Sfr fr + Z.of_nat 336 +
                     Z.of_nat (length (cells_bytes (p3_shc b5 b6 b7 b8 b9 b19 b20 b21 b22 b23))))
              with (Sfr fr + 365) by (cbn; lia).
            apply (bytes_at_transport rsegs [(Sfr fr + 336, Sfr fr + 365)] mem msh (Sfr fr + 365) _ Hsh3 MU1).
            p3_dj.
      - rewrite !length_app, Hl1, Hl3. reflexivity. }
    assert (HFRAs : FRA B APIf ra g fr [] regs msh md).
    { apply (sl_fr_meta B APIf ra empty FF g fr [] regs regs mem msh md [(Sfr fr + 336, Sfr fr + 365)]
        HFRA MU1 WM1 HROs HDJs HAHs HSTKs Happ HGT Hshs).
      - intros x Hx Hnb Hnsh. p3_out.
      - intros A0 HA0 HA0r x Hx. rewrite (p3_A0 regs A A0 Hr9 HAb HA0 HA0r) in Hx. p3_out.
      - intros x Hx. p3_out.
      - intros A0 HA0 HA0r x Hx. rewrite (p3_A0 regs A A0 Hr9 HAb HA0 HA0r) in Hx. p3_out.
      - intros x Hx. left. p3_out.
      - intros a Hin. apply (addr1_munch [(Sfr fr + 336, Sfr fr + 365)] mem msh a MU1); [|exact (HAG a Hin)].
        cbn [Frame.outside]. split; [|exact I].
        pose proof (p3_ag_range a Hin) as Har. rewrite EK9 in HGT.
        clear - Har HGT. unfold Sfr, shadow_addr, ASAN_K in *. Z.div_mod_to_equations. lia.
      - reflexivity.
      - reflexivity.
      - reflexivity.
      - reflexivity.
      - reflexivity.
      - reflexivity.
      - reflexivity. }
    (* FRA across the two calls (sl_fr_cl) *)
    assert (HAWc : all_app [(fr + 2880, fr + 2880 + 35); (spv - REAC_IDENTITY_INIT_K, spv);
                            (fr + 2688, fr + 2688 + 38)]).
    { cbn [all_app]. split; [|split; [|split; [|exact I]]].
      - intros a Ha. apply Happ. lia.
      - intros a Ha. right. lia.
      - intros a Ha. apply Happ. lia. }
    assert (HDJc : AsanRTInv.rt_disjoint [(fr + 2880, fr + 2880 + 35); (spv - REAC_IDENTITY_INIT_K, spv);
                                          (fr + 2688, fr + 2688 + 38)]).
    { unfold AsanRTInv.rt_disjoint, RT_LO, RT_HI, RT_GOT_AF, RT_AF, RT_GOT_VERB, RT_VERB,
        RT_GOT_CF, RT_CF, RT_TSDI, RT_TSDK, RT_PGSZ, RT_TP, RT_TSDMAIN, RT_REAL_LO, RT_REAL_HI,
        RT_IMAP, RT_IMEM, RT_MUG, RT_AGLOB, RT_AGLOB_LEN. cbn [Frame.disjoint_from].
      repeat split; (lia || exact I). }
    (* the entry-anchored slot window after the calls: the callee window, the object and first.sroa.7 read
       back *)
    assert (HWIN1 : stk rsegs mem' (g_S g - AFw.SLOT_STACK) (g_S g)).
    { apply (fl_stk [(Sfr fr + 336, Sfr fr + 365); (spv - REAC_IDENTITY_INIT_K, spv);
                     (fr + 2688, fr + 2688 + 38); (fr + 2880, fr + 2880 + 35)]
               mem mem' (g_S g - AFw.SLOT_STACK) (g_S g) Hwin MUall WMall).
      intros x Hx.
      destruct (p3_in4 (Sfr fr + 336) (Sfr fr + 365) (spv - REAC_IDENTITY_INIT_K) spv
                  (fr + 2688) (fr + 2688 + 38) (fr + 2880) (fr + 2880 + 35) x) as [Hin|[Hin|[Hin|[Hin|Hout]]]].
      - exfalso. lia.
      - right. exact (rd_of_stk mem' (spv - FN_STACK) spv ST2 x ltac:(lia)).
      - right. pose proof (stk_of_rw_cells rsegs mem' (fr + 2688) [CB 38 (repeat (Z_to_bv 8 0) 38)] RW2) as Hst.
        exact (rd_of_stk mem' (fr + 2688) (fr + 2688 + 38) Hst x Hin).
      - right. pose proof (stk_of_rw_cells rsegs mem' (fr + 2880) [CB 35 (repeat (Z_to_bv 8 0) 35)] RWF2) as Hst.
        exact (rd_of_stk mem' (fr + 2880) (fr + 2880 + 35) Hst x Hin).
      - left. exact Hout. }
    (* the calls write below stklo only frame-body bytes, so the side arm's frame record is kept *)
    assert (HREC : FSREC fr msh -> FSREC fr mem').
    { apply (fra_fsrec_stklo B APIf ra g fr [] regs msh mem' md
               [(fr + 2880, fr + 2880 + 35); (spv - REAC_IDENTITY_INIT_K, spv); (fr + 2688, fr + 2688 + 38)]
               HFRAs MU2).
      intros x Hx Hnb. rewrite HSTKs in Hx. p3_out. }
    assert (HFRA1 : FRA B APIf ra g fr [] regs'' mem' md).
    { apply (sl_fr_cl B APIf ra empty FF g fr [] regs regs'' msh mem' md
        [(fr + 2880, fr + 2880 + 35); (spv - REAC_IDENTITY_INIT_K, spv); (fr + 2688, fr + 2688 + 38)]
        HFRAs MU2 WM2 RO2 HAWc HDJc HAH1 ltac:(rewrite HSTK1, HSTKs; reflexivity)).
      - intros x Hx. p3_out.
      - intros x Hx. p3_out.
      - intros A0 HA0 HA0r x Hx. rewrite (p3_A0 regs A A0 Hr9 HAb HA0 HA0r) in Hx. p3_out.
      - intros x Hx. p3_out.
      - intros x Hx. p3_out.
      - intros A0 HA0 HA0r x Hx. rewrite (p3_A0 regs A A0 Hr9 HAb HA0 HA0r) in Hx. p3_out.
      - exact HWIN1.
      - exact HREC.
      - exact E2.
      - exact E3.
      - exact E4.
      - exact E8.
      - exact E9.
      - exact E19.
      - exact E26. }
    assert (HFRA' : FRA B APIf ra g fr [] regs'' mem' md').
    { apply (sl_fra_move B APIf ra g fr [] regs'' regs'' mem' md md' HFRA1); try reflexivity. exact Hmat. }
    (* ENT: the run writes only the frame's shadow, the slot window and the frame (ent_store), then ent_mat *)
    assert (HENT1 : ENT APIf g [] mem' md).
    { eapply ent_store with (W := [(Sfr fr + 336, Sfr fr + 365); (spv - REAC_IDENTITY_INIT_K, spv);
                                   (fr + 2688, fr + 2688 + 38); (fr + 2880, fr + 2880 + 35)]);
        [exact HENT | exact HFRA | exact MUall | | exact HSTK1 | exact Hhi1
        | exact (fun a _ Ho => proj2 (Hown1 a) Ho)].
      intros x Hx.
      destruct (p3_in4 (Sfr fr + 336) (Sfr fr + 365) (spv - REAC_IDENTITY_INIT_K) spv
                  (fr + 2688) (fr + 2688 + 38) (fr + 2880) (fr + 2880 + 35) x) as [Hin|[Hin|[Hin|[Hin|Hout]]]].
      - right. right. right. lia.
      - right. left. lia.
      - right. right. left. lia.
      - right. right. left. lia.
      - left. exact Hout. }
    assert (HENT' : ENT APIf g [] mem' md') by (eapply ent_mat; [exact HENT1 | exact Hmat]).
    (* the cells the exit names: none of them meets the write set *)
    assert (HOURlen : Z.of_nat (length (OUR (g_in g))) = 6).
    { unfold OUR. rewrite length_map, length_seq. reflexivity. }
    assert (HOUR' : OURb g fr mem').
    { unfold OURb in *.
      apply (bytes_at_transport rsegs [(Sfr fr + 336, Sfr fr + 365); (spv - REAC_IDENTITY_INIT_K, spv);
               (fr + 2688, fr + 2688 + 38); (fr + 2880, fr + 2880 + 35)] mem mem' (fr + 2624) (OUR (g_in g))
               HOUR MUall).
      rewrite HOURlen. p3_dj. }
    assert (RW192' : rw_cells rsegs mem' (A + 192) [C8 (Z_to_bv 64 (fr + 2768))]).
    { apply (rw_cells_transport rsegs [(Sfr fr + 336, Sfr fr + 365); (spv - REAC_IDENTITY_INIT_K, spv);
               (fr + 2688, fr + 2688 + 38); (fr + 2880, fr + 2880 + 35)] mem mem' (A + 192) _ RW192 MUall WMall).
      p3_dj. }
    assert (RWd' : rw_cells rsegs mem' (fr + 2768) [CB 72 junk]).
    { apply (rw_cells_transport rsegs [(Sfr fr + 336, Sfr fr + 365); (spv - REAC_IDENTITY_INIT_K, spv);
               (fr + 2688, fr + 2688 + 38); (fr + 2880, fr + 2880 + 35)] mem mem' (fr + 2768) _ RWd MUall WMall).
      p3_dj. }
    assert (RWjy' : rw_cells rsegs mem' (fr + 3040) [CB 1 jy]).
    { apply (rw_cells_transport rsegs [(Sfr fr + 336, Sfr fr + 365); (spv - REAC_IDENTITY_INIT_K, spv);
               (fr + 2688, fr + 2688 + 38); (fr + 2880, fr + 2880 + 35)] mem mem' (fr + 3040) _ RWjy MUall WMall).
      p3_dj. }
    assert (RWj2' : rw_cells rsegs mem' (fr + 3056) [CB 32 junk2]).
    { apply (rw_cells_transport rsegs [(Sfr fr + 336, Sfr fr + 365); (spv - REAC_IDENTITY_INIT_K, spv);
               (fr + 2688, fr + 2688 + 38); (fr + 2880, fr + 2880 + 35)] mem mem' (fr + 3056) _ RWj2 MUall WMall).
      p3_dj. }
    assert (Q280' : q64 mem' (A + 280) (fr + 3040)).
    { unfold q64 in *.
      apply (bytes_at_transport rsegs [(Sfr fr + 336, Sfr fr + 365); (spv - REAC_IDENTITY_INIT_K, spv);
               (fr + 2688, fr + 2688 + 38); (fr + 2880, fr + 2880 + 35)] mem mem' (A + 280) _ Q280 MUall).
      rewrite length_le8. p3_dj. }
    assert (Q240' : q64 mem' (A + 240) (fr + 3056)).
    { unfold q64 in *.
      apply (bytes_at_transport rsegs [(Sfr fr + 336, Sfr fr + 365); (spv - REAC_IDENTITY_INIT_K, spv);
               (fr + 2688, fr + 2688 + 38); (fr + 2880, fr + 2880 + 35)] mem mem' (A + 240) _ Q240 MUall).
      rewrite length_le8. p3_dj. }
    (* the 72 bytes at fr + 2768 are addressable: their 9 shadow bytes are 0 after the stores *)
    assert (HB346 : bytes_at rsegs msh (Sfr fr + 346) (repeat (Z_to_bv 8 0) (Z.to_nat 9))).
    { assert (HB' : bytes_at rsegs msh (Sfr fr + 336)
                      ([Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 6; b5; b6; b7; b8; b9] ++
                       (repeat (Z_to_bv 8 0) (Z.to_nat 9) ++
                        [b19; b20; b21; b22; b23; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0;
                         Z_to_bv 8 3]))) by exact HB29.
      apply bytes_at_app in HB'. destruct HB' as [_ HB'].
      apply bytes_at_app in HB'. destruct HB' as [HB' _].
      match type of HB' with bytes_at _ _ ?a _ => replace a with (Sfr fr + 346) in HB' by (cbn; lia) end.
      exact HB'. }
    assert (HADs : addressable msh (fr + 2768) (8 * 9)).
    { apply p3_addr_zero; [| lia | lia | lia | intros i Hi; apply Happ; lia |].
      - clear -Hfr8. Z.div_mod_to_equations. lia.
      - replace (fr + 2768) with (fr + 8 * 346) by lia. rewrite Eshad. exact HB346. }
    assert (HAD' : addressable mem' (fr + 2768) 72)
      by exact (sl_addr_keep msh mem' [(fr + 2880, fr + 2880 + 35); (spv - REAC_IDENTITY_INIT_K, spv);
                                       (fr + 2688, fr + 2688 + 38)] (fr + 2768) 72 HADs MU2 HAWc).
    (* the 38 object bytes at fr + 2688 are addressable after the stores (shadow 0,0,0,0,6) and after the calls
       (they write app bytes only), so the 17 bytes at fr + 2691 are *)
    assert (HADo : addressable msh (fr + 2688) 38).
    { apply HADDR.
      assert (HB' : bytes_at rsegs msh (Sfr fr + 336)
                      ([Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 6] ++
                       [b5; b6; b7; b8; b9; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0;
                        Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; b19; b20; b21; b22; b23;
                        Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 3])) by exact HB29.
      apply bytes_at_app in HB'. exact (proj1 HB'). }
    assert (HAD38 : addressable mem' (fr + 2688) 38)
      by exact (sl_addr_keep msh mem' [(fr + 2880, fr + 2880 + 35); (spv - REAC_IDENTITY_INIT_K, spv);
                                       (fr + 2688, fr + 2688 + 38)] (fr + 2688) 38 HADo MU2 HAWc).
    assert (HAD17 : addressable mem' (fr + 2691) 17).
    { replace (fr + 2691) with (fr + 2688 + 3) by lia.
      apply (p3_addr_sub mem' (fr + 2688) 38 3 17 HAD38); lia. }
    (* cut bundle round 4: first.sroa.7's 35 bytes at fr + 2880 are addressable after the stores (shadow
       S(fr) + 360 .. 364 = 0,0,0,0,3, from 0x81b40 / 0x81b44 / 0x81b5c / 0x81b60 / 0x81b64) and after the calls *)
    assert (HADf : addressable msh (fr + 2880) 35).
    { apply HADDRf.
      assert (HB' : bytes_at rsegs msh (Sfr fr + 336)
                      ([Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 6;
                        b5; b6; b7; b8; b9; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0;
                        Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; b19; b20; b21; b22; b23] ++
                       [Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 3])) by exact HB29.
      apply bytes_at_app in HB'. destruct HB' as [_ HB'].
      match type of HB' with bytes_at _ _ ?a _ => replace a with (Sfr fr + 360) in HB' by (cbn; lia) end.
      exact HB'. }
    assert (HAD2880 : addressable mem' (fr + 2880) 35)
      by exact (sl_addr_keep msh mem' [(fr + 2880, fr + 2880 + 35); (spv - REAC_IDENTITY_INIT_K, spv);
                                       (fr + 2688, fr + 2688 + 38)] (fr + 2880) 35 HADf MU2 HAWc).
    (* the spill [A + 144] = fr + 2688: s1 = A, and [A + 144] is real stack at or above sp, above the frame *)
    assert (EA1 : A1 = A).
    { unfold rg in HA1. pose proof Q144 as Hq. unfold q64 in Hq. apply bytes_at_bound in Hq.
      rewrite length_le8 in Hq. rewrite Hr9 in HA1. apply (f_equal (@bv_unsigned 64)) in HA1.
      rewrite !Z_to_bv_unsigned in HA1. unfold bv_wrap, bv_modulus in HA1.
      change (2 ^ Z.of_N 64)%Z with (2 ^ 64)%Z in HA1.
      clear - HA1 Hq HAS HAPP HAb EK5. revert HA1 Hq. Z.div_mod_to_equations. lia. }
    subst A1.
    assert (Q144' : q64 mem' (A + 144) (fr + 2688)).
    { unfold q64 in *.
      apply (bytes_at_transport rsegs [(Sfr fr + 336, Sfr fr + 365); (spv - REAC_IDENTITY_INIT_K, spv);
               (fr + 2688, fr + 2688 + 38); (fr + 2880, fr + 2880 + 35)] mem mem' (A + 144) _ Q144 MUall).
      rewrite length_le8. p3_dj. }
    (* the exit cut Inv_A81b80 *)
    rewrite <- SEGS. apply Hexit.
    exists regs'', mem', md', fr.
    split; [reflexivity|]. split; [exact HFRA'|]. split; [exact HENT'|].
    split; [exact Hgn|]. split; [exact HOUR'|].
    (* CUR: the run keeps s6 and s9 (the callee contracts keep the s registers) *)
    split.
    { destruct HCUR as (Hc0 & H22 & H25). unfold CUR, rg in *.
      split; [exact Hc0|]. split; [rewrite E22; exact H22 | rewrite E25; exact H25]. }
    (* push 13: PRO (the write set is 29 frame-shadow bytes from S(fr) + 336, the callee window at or above stklo
       and below A, and the frame bytes at fr + 2688 / fr + 2880: P1's pro_fra) *)
    split.
    { assert (MUL : LibFr.munch [(Sfr fr + 336, Sfr fr + 365); (spv - REAC_IDENTITY_INIT_K, spv);
                                 (fr + 2688, fr + 2688 + 38); (fr + 2880, fr + 2880 + 35)] mem mem').
      { first [exact MUall | exact (proj2 (fr_munch_ul _ mem mem') MUall)
                          | exact (proj1 (fr_munch_ul _ mem mem') MUall)]. }
      apply (pro_fra B APIf ra g fr [] regs regs'' mem mem' md _ A HFRA HPRO Hr9 HAb MUL E9).
      apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]]]];
        unfold pro_iv; cbn [fst snd]; lia. }
    split; [exists A; split; [unfold rg; rewrite E9; exact Hr9 | exact Q144']|].
    split; [exact HAD17|].
    (* push 14D: the two record ranges this run makes addressable, (fragb fr, 72) = (fr + 2768, 72) and
       (fr + 2688, 38) *)
    split; [exact HAD'|]. split; [exact HAD38|].
    (* IDBe: the init post's 38 zero bytes at fr + 2688 are ID0 *)
    split.
    { unfold IDBe, RcIdentModel.ID0, RcIdentModel.zb, RcIdentModel.ID_SIZE.
      destruct RW2 as [[_ HB] _]. cbn [cells_bytes cbytes] in HB. rewrite app_nil_r in HB. exact HB. }
    exists (fr + 2768), spv, A, junk.
    cbv zeta.
    split; [rewrite E2; exact Hr2|]. split; [rewrite E9; exact Hr9|].
    split; [exact HAb|]. split; [lia|]. split; [exact Hspvb|].
    split; [exact RW192'|]. split; [exact RWd'|]. split; [exact HAD'|].
    split; [right; apply Happ; lia|]. split; [apply Happ; lia|].
    split; [right; lia|]. split; [lia|].
    split; [intros x Hx; p3_out|].
    split; [intros x Hx; p3_out|].
    split; [intros A0 HA0 HA0r x Hx; rewrite E9 in HA0;
            rewrite (p3_A0 regs A A0 Hr9 HAb HA0 HA0r) in Hx; p3_out|].
    split; [intros A0 HA0 HA0r x Hx; rewrite E9 in HA0;
            rewrite (p3_A0 regs A A0 Hr9 HAb HA0 HA0r) in Hx; p3_out|].
    split; [intros x Hx; p3_out|].
    split; [intros x Hx; p3_out|].
    split; [intros x Hx; rewrite HOURlen in Hx; p3_out|].
    split.
    { cbn [all_app]. split; [|split; [|exact I]].
      - intros a Ha. apply Happ. lia.
      - intros a Ha. right. lia. }
    split.
    { unfold AsanRTInv.rt_disjoint, RT_LO, RT_HI, RT_GOT_AF, RT_AF, RT_GOT_VERB, RT_VERB,
        RT_GOT_CF, RT_CF, RT_TSDI, RT_TSDK, RT_PGSZ, RT_TP, RT_TSDMAIN, RT_REAL_LO, RT_REAL_HI,
        RT_IMAP, RT_IMEM, RT_MUG, RT_AGLOB, RT_AGLOB_LEN. cbn [Frame.disjoint_from].
      repeat split; (lia || exact I). }
    split; [reflexivity|]. split; [exact Q280'|]. split; [exact Q240'|].
    split; [exists jy, junk2; split; [exact RWjy' | exact RWj2'] | exact HAD2880].
Qed.

End P3W.
