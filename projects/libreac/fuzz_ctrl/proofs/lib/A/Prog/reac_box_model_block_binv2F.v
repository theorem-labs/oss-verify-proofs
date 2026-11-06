(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/jsoncons/fuzz_bigint/lib/L5TCopyS.v, with its module paths and module names changed; 731 of its 745 lines of code are new or changed and 234 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/A/Prog/reac_box_model_block_binv2.v; 415 of its 921 lines of code are new or changed and 239 lines of the source are left out. *)
(* Footprint (_F) re-run of reac_box_model_block_binv2.v at a working branch d69f7c708f6 (proved v1.9
   run of record) over lib/Lib/StepF, from its proof scripts; the script edits include `hide_sec.`, rng and narrowed-shadow steps, and eleven declarations with a proof are new (five helpers, two OfF bounds and the four cl_*_of_F corollaries) with seven Lets.
   Image: fuzz_ctrl.asan (libreac v1.9.0), ELF sha256
   78efaeda1de51f8cb9208f86af7467cc8cb84e10c53295e7b6c3dce28ddcbebd. FACTS ed6b6b7b0ab.
   Const cells checked against the v1.9.0 image bytes: none read (the four runs of this file take no step of this
   image: each one cuts at its call and hands the stretch [call .. ret) to the callee's footprint contract, so the
   only cells read are the callee's own, inside the regions the contract asks for).

   The four runtime-call wrappers of reac_box_model_block_binv2.v in footprint form:
     cl_ms_F      __asan_memset(o + kk, v, nn)     applies HMSF (asan_memset_cF.asan_memset_contract_F)
     cl_mc_F      __asan_memcpy(o + kk, SS, nn)    applies HMCF (asan_memcpy_cF.asan_memcpy_contract_F)
     cl_ms_loc_F  __asan_memset(A + dd, v, nn)     applies HMSF
     cl_bd_F      build_dt1_single(o, v, SS, nn)   applies HBDF (build_dt1_single_c.build_dt1_single_contract_F)
   where the proved file applies HMS / HMC / HBD. These are the only four sites of this family at which a callee
   contract is applied in _F form (reac_box_model_block_cases2F.v's a4_cl_mc_loc_F is the fifth).
   Route (a) conditions (lead 22:15-22:18Z, a Theorem Labs lane 22:20Z), obeyed here except condition 1:
     1. each _F is a MECHANICAL re-derivation of an already-PROVED v1.9 run: the same proof script over StepF, and
        no new proof obligation;
     2. the _F output feeds ONLY the ported cgif-form walk (no W_cutfree_ok, no cut-free twin, no LSCPS join, no
        top-level claim);
     3. the source runs are on ctrl's v1.9 record (FACTS ed6b6b7b0ab), with no stale AsanRT / off_img literal /
        wrong-image cell; the re-run's const cells are checked against fuzz_ctrl's v1.9.0 image bytes;
     4. every _F carries provenance in its header and goes to the auditor a Theorem Labs lane, who signs it against its
        proved run before it counts;
     5. a StepF "uncovered access" error means STOP: report it, never widen the footprint to make it pass.

   The post is a parameter (Variable Q, Hypothesis HKR : bmb_KR Q of reac_box_model_block_epiF.v), as in every S2
   file of the family: these four runs conclude the fixed ret post Q0 in the proved file, and the cgif-form walk
   cuts S2 at the flag release 0x864f8.

   Footprint premises. Every region these four runs touch is already named by the section's data-region facts
   (a Theorem Labs lane, interface decision (B)): the box [o, o + 32) and its shadow cover (RO / ROs), the window
   [sp - 4272, sp) and its shadow cover (Rwin / Rwsh), which hold the 56 locals at A and the helper frames, the
   image [IMG_LO, IMG_HI) (Rimg), which holds the runtime words [RT_LO, RT_HI), and rng_bytes RNG (Rby).  The only
   per-lemma premises are the three of the COPY SOURCE of cl_mc_F and cl_bd_F, a range the lemma's own premises name
   and whose region only the caller knows (the row at p, a JOIN block, the 56 locals or the ASan frame):
     rng RNG SS (Z.of_nat nn) -> sh_cover RNG SS (Z.of_nat nn) -> (forall a, sh_word_on SS (Z.of_nat nn) a -> the audited shadow region a).
   No other rng premise is added, and no numeral is new: the only numerals here are the ones of the proved file
   (4272, 32, 56, 2208 / 2224 / 2272 through ASAN_MEMSET_K / ASAN_MEMCPY_K / BUILD_DT1_SINGLE_K) and the bounds of
   IMG_LO / IMG_HI / RT_LO / RT_HI of lib/A/Prog/ImgBounds.v and lib/A/AsanRT.v. *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Sem.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac Bytes ZBridge.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog Require Import RcModel RcLib RcRec RcRecLib RcBox RcBoxLib
  RcSynth RcSynthLib RcLay RcAsan RcAsanLib.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A Require Import Img0 AsanRT ShadowRwOn.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog Require Import RcAsanRT RcAsanFP RcAsanFPLib
  asan_stack_malloc_c asan_memset_c asan_memcpy_c build_dt1_single_c reac_box_model_block_c
  reac_box_model_block_base reac_box_model_block_epi reac_box_model_block_binv reac_box_model_block_binv2.
(* the shared footprint vocabulary and the shared _F callee contracts (a Theorem Labs lane), and the footprint twins of the
   files this one's original requires *)
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import RngBytes.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog Require Import ImgBounds asan_memset_cF asan_memcpy_cF
  rng_asan sh_word_on asan_memset_c_on asan_memset_cF_on asan_memcpy_c_on asan_memcpy_cF_on reac_box_model_block_c_on
  reac_box_model_block_cF reac_box_model_block_baseF reac_box_model_block_epiF reac_box_model_block_binvF.
(* Last: StepF's step / store_done / if_false (evtF goals) shadow Step's and Tac's (evt goals). *)
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import ExecF StepF.
Import ListNotations.
Open Scope Z_scope.

Module B := reac_box_model_block_base.
Module BEPI := reac_box_model_block_epi.
Module BINV := reac_box_model_block_binv.
Module BINV2 := reac_box_model_block_binv2.
Module BEPIF := reac_box_model_block_epiF.
Module BASEF := reac_box_model_block_baseF.
Module BINVF := reac_box_model_block_binvF.
Module C_ON := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog.reac_box_model_block_c_on.

From Ltac2 Require Import Ltac2.

(* The section-closing generalization abstracts each lemma of Section Main over the section variables and hypotheses
   it uses, in declaration order, under their own names. inst c applies c to the hypotheses of the current context
   that carry the names of c's leading binders, and stops at the first binder whose name is not a hypothesis. *)
Ltac2 rec inst_go (c : constr) (t : constr) (acc : constr list) :=
  let fin () := match acc with
                | [] => c
                | _ => Constr.Unsafe.make (Constr.Unsafe.App c (Array.of_list (List.rev acc)))
                end in
  match Constr.Unsafe.kind t with
  | Constr.Unsafe.Prod bnd body =>
      match Constr.Binder.name bnd with
      | Some id =>
          match Control.case (fun () => Control.hyp id) with
          | Val hv => let (h, _) := hv in inst_go c (Constr.Unsafe.substnl [h] 0 body) (h :: acc)
          | Err _ => fin ()
          end
      | None => fin ()
      end
  | _ => fin ()
  end.

Ltac2 inst (c : constr) := inst_go c (Constr.type c) [].

Ltac2 Notation "inst_exact" c(constr) := let r := inst c in exact $r.

Set Default Proof Mode "Classic".

(* An opaque wrapper: a hypothesis of type mb_hide T is invisible to lia. *)
Definition mb_hide (P : Prop) : Prop := P.

(* ------------------------------------------------------------------------------------------------------------ *)
(* Footprint arithmetic: a sub-range of a covered range is covered, and sh_cover (reac_box_model_block_cF.v) is
   the n > 0 case of the sh_word_rng of the two shared callee contracts (same text: the 8-aligned shadow word
   span of [a, a + n)). No run fact is used here. *)

Lemma shc_sub : forall (RNG : footprint) (a n a' n' : Z),
  sh_cover RNG a n -> a <= a' -> 0 < n' -> a' + n' <= a + n -> sh_cover RNG a' n'.
Proof.
  intros RNG a n a' n' H H1 H2 H3. unfold sh_cover, shadow_addr in *.
  eapply rng_sub; [exact H | Z.div_mod_to_equations; lia | Z.div_mod_to_equations; lia].
Qed.

Lemma shw_ms_of_shc : forall (RNG : footprint) (a n : Z),
  0 < n -> sh_cover RNG a n -> rng_asan.sh_word_rng RNG a n.
Proof.
  intros RNG a n Hn H. right.
  unfold rng_asan.sh_al8_lo, rng_asan.sh_al8_hi. unfold sh_cover in H. exact H.
Qed.

Lemma shw_mc_of_shc : forall (RNG : footprint) (a n : Z),
  0 < n -> sh_cover RNG a n -> rng_asan.sh_word_rng RNG a n.
Proof.
  intros RNG a n Hn H. right.
  unfold rng_asan.sh_al8_lo, rng_asan.sh_al8_hi. unfold sh_cover in H. exact H.
Qed.

Section MainF.
  Variables (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (m : word -> option byte) (p b o FS off A : Z) (row nb ob : list byte).
  (* the callee-contract hypotheses in their _F forms (the shared contracts of a Theorem Labs lane) *)
  Hypothesis HMSF : asan_memset_cF_on.asan_memset_contract_F_on.
  Hypothesis HMCF : asan_memcpy_cF_on.asan_memcpy_contract_F_on.
  Hypothesis HBDF : build_dt1_single_contract_F_on.
  Hypothesis Hoff : off = ASAN_K.
  Hypothesis HA : A = (bv_unsigned sp - 160) / 32 * 32.
  Hypothesis HS16 : bv_unsigned sp mod 16 = 0.
  Hypothesis ST0 : stk rsegs m (bv_unsigned sp - 4272) (bv_unsigned sp).
  Hypothesis MI0 : mem_inv rsegs m.
  Hypothesis AC0 : asan_cells m.
  (* Route (C): the shadow region of this function (reac_box_model_block_c_on.v:38), not the universal shadow_rw. *)
  Hypothesis SR0 : A.ShadowRwOn.shadow_rw_on (C_ON.reac_box_model_block_shadow_R (bv_unsigned sp) FS p b o row nb) m.
  Hypothesis HHM : HIGHMEM_BEG <= bv_unsigned sp - 4272.
  Hypothesis HAE : bv_unsigned sp <= APPMEM_END.
  Hypothesis AW0 : addressable m (bv_unsigned sp - 4272) 4272.
  Hypothesis FP0 : fp [0%nat] m (bv_unsigned tp) FS (bv_unsigned sp - 4272) (bv_unsigned sp)
    (reac_box_model_block_W o (bv_unsigned sp)) (reac_box_model_block_D p o).
  Hypothesis TLS0 : reac_box_model_block_tls m (bv_unsigned tp) FS (bv_unsigned sp - REAC_BOX_MODEL_BLOCK_K) (bv_unsigned sp).
  Hypothesis Rp : 0 <= p < 2^64.
  Hypothesis Rb : 0 <= b < 2^64.
  Hypothesis Ro : 0 <= o < 2^64.
  Hypothesis HP : p <> 0 -> p mod 8 = 0 /\ length row = 296%nat /\ bytes_at rsegs m p row /\
    (bv_unsigned sp <= p \/ p + 296 <= bv_unsigned sp - 4272) /\ (o = 0 \/ o + 32 <= p \/ p + 296 <= o).
  Hypothesis HN : p <> 0 -> (b = 5 \/ b = 6) -> has row <> 0 -> rname row <> 0 ->
    name_ok nb /\ bytes_at rsegs m (rname row) nb /\
    (bv_unsigned sp <= rname row \/ rname row + Z.of_nat (length nb) <= bv_unsigned sp - 4272) /\
    (o = 0 \/ o + 32 <= rname row \/ rname row + Z.of_nat (length nb) <= o).
  Hypothesis HO : o <> 0 -> rw_cells rsegs m o [CB 32 ob] /\
    (bv_unsigned sp <= o \/ o + 32 <= bv_unsigned sp - 4272) /\ (o + 32 <= JOIN_0013 \/ JOIN_0014 + 32 <= o).
  Hypothesis AP : p <> 0 -> addressable m p 296.
  Hypothesis ANB : p <> 0 -> (b = 5 \/ b = 6) -> has row <> 0 -> rname row <> 0 ->
    addressable m (rname row) (Z.of_nat (length nb)).
  Hypothesis AO : o <> 0 -> addressable m o 32 /\ app_mem (o + 32) /\ (o + 32 <= RT_LO \/ RT_HI <= o).
  Hypothesis AJ1 : b = 1 -> addressable m JOIN_0014 32.
  Hypothesis AJ2 : b = 2 -> addressable m JOIN_0013 32.
  Hypothesis NDJ : p <> 0 -> (b = 5 \/ b = 6) -> has row <> 0 -> rname row <> 0 ->
    fp_dj [(rname row, rname row + Z.of_nat (length nb))] (fp_w [0%nat] FS).

  (* The footprint and the regions the runs of this function read or write (the nine of
     reac_box_model_blockF.v (at head lib/A/Prog/reac_box_model_blockF.v:159 and :161-168; written on a working branch 3c9fcc93205)), then the data-region facts every F file of this family carries
     (a Theorem Labs lane, interface decision (B)). *)
  Variable RNG : footprint.
  Hypothesis Rimg : rng RNG 0x10000 0x5ee000.
  Hypothesis Rwin : rng RNG (bv_unsigned sp - REAC_BOX_MODEL_BLOCK_K) REAC_BOX_MODEL_BLOCK_K.
  Hypothesis Rwsh : sh_cover RNG (bv_unsigned sp - REAC_BOX_MODEL_BLOCK_K) REAC_BOX_MODEL_BLOCK_K.
  Hypothesis Rtp88 : rng RNG (bv_unsigned tp - 88) 8.
  Hypothesis Rtp8 : rng RNG (bv_unsigned tp - 8) 24.
  Hypothesis Rtls : reac_box_model_block_tls_rng RNG m (bv_unsigned tp).
  Hypothesis RFSh : rng RNG FS (fs_frame FS 0%nat 0 - FS).
  Hypothesis RFSw : rng_ivls RNG (tl (fp_w [0%nat] FS)).
  Hypothesis RFSsh : rng RNG (shadow_addr (fs_frame FS 0%nat 0)) (fs_M 0%nat * fs_B 0%nat / 8).
  Hypothesis Rby : rng_bytes RNG.
  Hypothesis Rwsw : rng_asan.sh_word_rng RNG (bv_unsigned sp - REAC_BOX_MODEL_BLOCK_K) REAC_BOX_MODEL_BLOCK_K.
  Hypothesis RP : p <> 0 -> rng RNG p 296.
  Hypothesis RPs : p <> 0 -> sh_cover RNG p 296.
  Hypothesis RO : o <> 0 -> rng RNG o 32.
  Hypothesis ROs : o <> 0 -> sh_cover RNG o 32.
  Hypothesis RN : p <> 0 -> (b = 5 \/ b = 6) -> has row <> 0 -> rname row <> 0 ->
    rng RNG (rname row) (Z.of_nat (length nb)).
  Hypothesis RNs : p <> 0 -> (b = 5 \/ b = 6) -> has row <> 0 -> rname row <> 0 ->
    sh_cover RNG (rname row) (Z.of_nat (length nb)).
  Hypothesis RJ13s : b = 2 -> sh_cover RNG JOIN_0013 32.
  Hypothesis RJ14s : b = 1 -> sh_cover RNG JOIN_0014 32.

  (* The post is a parameter: S2 of the cgif-form walk stops at the flag release 0x864f8, before the ret post Q0.
     bmb_KR Q is the statement of reac_box_model_block_epi.v's `epi` with Q0 replaced by Q and evt rsegs by
     evtF rsegs RNG (reac_box_model_block_epiF.v), taken at this section's variables. *)
  Let bmb_KR := ltac2:(inst_exact @BEPIF.bmb_KR).
  (* The post is indexed by the FK data of the run (the lead 03:4xZ, for BmbGlue): the glue can
     discharge the epi obligation only for the frame cgif allocated, on the fake arm. *)
  Variable Q : Z -> Z -> Z -> Z -> Z -> word -> machine_state -> Prop.
  Hypothesis HKR : bmb_KR Q.

  (* The definitions of reac_box_model_block_base.v and reac_box_model_block_binv.v at this section's variables. *)
  Notation FK := (B.FK FS A).
  Notation Wf := (B.Wf sp FS).
  Notation EBW := (B.EBW sp p o FS).
  Notation SAVES := (B.SAVES ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11).
  Notation BI := (B.BI ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m FS).
  Notation EB := (B.EB ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m p b o FS row nb).
  Notation Q0 := (B.Q0 ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m p b o FS row nb).
  Notation BV := (BINVF.BV_F ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m p b o FS A row nb).
  Notation RB := (BINVF.RB_F sp gp tp p o off A).

  (* The pure lemmas of reac_box_model_block_base.v, reac_box_model_block_binv.v and
     reac_box_model_block_binv2.v at this section's variables and hypotheses. *)
  (* Route (C): every Section Main lemma of the proved _binv.v / _binv2.v carries SR0 (About), so each comes from
     its narrowed twin in reac_box_model_block_binvF.v; only HA1 of _base.v does not and stays the proved one.
     rw_upd2_F and app_loc_F are the two facts of the proved _binv2.v this file needs: they are re-proved below. *)
  Let HA1 := ltac2:(inst_exact @B.HA1).
  Let fk_facts := ltac2:(inst_exact @BASEF.fk_facts_F).
  Let rw1 := ltac2:(inst_exact @BINVF.rw1_F).
  Let djw := ltac2:(inst_exact @BINVF.djw_F).
  Let bv_jx := ltac2:(inst_exact @BINVF.bv_jx_F).
  Let bv_store := ltac2:(inst_exact @BINVF.bv_store_F).
  Let bv_lstore := ltac2:(inst_exact @BINVF.bv_lstore_F).
  Let bv_fstore := ltac2:(inst_exact @BINVF.bv_fstore_F).
  Let app_o := ltac2:(inst_exact @BINVF.app_o_F).
  Let spc_bounds := ltac2:(inst_exact @BINVF.spc_bounds_F).
  Let call_facts := ltac2:(inst_exact @BINVF.call_facts_F).

  (* Hide a hypothesis from lia (its disjunctions and implications make every lia call search them). *)
  Ltac hide H := let T := type of H in change (mb_hide T) in H.
  Ltac unhide H := unfold mb_hide in H.
  Ltac hide_sec := hide HP; hide HN; hide HO; hide AP; hide ANB; hide AO; hide AJ1; hide AJ2; hide NDJ;
    hide HA; hide HS16.



  (* Route (C) membership: the shadow a callee's own region names is inside R, this function's audited shadow
     region (reac_box_model_block_c_on.v:38). The box [o, o + 32) is R's fifth disjunct, the window its first. *)
  Lemma box_shadow_sub : forall (a : Z) (k n : nat), o <> 0 -> (k + n <= 32)%nat -> (1 <= n)%nat ->
    sh_word_on (o + Z.of_nat k) (Z.of_nat n) a ->
    C_ON.reac_box_model_block_shadow_R (bv_unsigned sp) FS p b o row nb a.
  Proof.
    intros a k n Ho0 Hkn Hn Ha. hide_sec.
    unfold C_ON.reac_box_model_block_shadow_R. right. right. right. right. left. split; [exact Ho0|].
    destruct Ha as (Hn0 & Hlo & Hhi).
    unfold sh_word_on, rng_asan.sh_al8_lo, rng_asan.sh_al8_hi, shadow_addr in *.
    split; [lia|]. Z.div_mod_to_equations; lia.
  Qed.

  Lemma win_shadow_sub : forall (a lo n : Z), bv_unsigned sp - REAC_BOX_MODEL_BLOCK_K <= lo -> 0 < n ->
    lo + n <= bv_unsigned sp -> sh_word_on lo n a ->
    C_ON.reac_box_model_block_shadow_R (bv_unsigned sp) FS p b o row nb a.
  Proof.
    intros a lo n Hlo0 Hn Hhi0 Ha. hide_sec.
    unfold C_ON.reac_box_model_block_shadow_R. left.
    destruct Ha as (Hn0 & Hlo & Hhi).
    unfold sh_word_on, rng_asan.sh_al8_lo, rng_asan.sh_al8_hi, shadow_addr, REAC_BOX_MODEL_BLOCK_K in *.
    split; [lia|]. Z.div_mod_to_equations; lia.
  Qed.

  (* A call that wrote exactly [AA + k, AA + k + n) of the cell at AA (and bytes outside the cell) updates it. *)
  Lemma rw_upd2_F : forall (mm mm' : word -> option byte) (AA : Z) (N kk nn : nat) (X Y : list byte) (W : list ivl),
    rw_cells rsegs mm AA [CB N X] -> (kk + nn <= N)%nat -> length Y = nn ->
    munch W mm mm' -> wmono rsegs mm mm' ->
    (forall x, AA <= x < AA + Z.of_nat N ->
       ~ (AA + Z.of_nat kk <= x < AA + Z.of_nat kk + Z.of_nat nn) -> outside W x) ->
    bytes_at rsegs mm' (AA + Z.of_nat kk) Y ->
    rw_cells rsegs mm' AA [CB N (upd_bytes X kk Y)].
  Proof.
    intros mm mm' AA N kk nn X Y W HC Hkn LY MU WM HOut HY. hide_sec.
    pose proof HC as [[Hwf HB] HW]. cbn [cells_wf cell_wf] in Hwf. destruct Hwf as [LX _].
    cbn [cells_bytes cbytes] in HB. rewrite app_nil_r in HB.
    destruct HB as (Hlo & Hhi & HBp). destruct HY as (_ & _ & HYp).
    split; [split|].
    - cbn [cells_wf cell_wf]. split; [rewrite upd_bytes_length by lia; exact LX | exact I].
    - cbn [cells_bytes cbytes]. rewrite app_nil_r.
      split; [exact Hlo|]. split; [rewrite upd_bytes_length by lia; exact Hhi|].
      intros i Hi. rewrite upd_bytes_length in Hi by lia.
      rewrite upd_bytes_nth by lia.
      destruct ((kk <=? i)%nat && (i <? kk + length Y)%nat)%bool eqn:Ec.
      + apply andb_true_iff in Ec. destruct Ec as [E1 E2].
        apply Nat.leb_le in E1. apply Nat.ltb_lt in E2.
        rewrite <- (HYp (i - kk)%nat ltac:(lia)). f_equal. f_equal. lia.
      + apply andb_false_iff in Ec.
        rewrite <- (HBp i ltac:(lia)). unfold mrd. rewrite (MU (wa (AA + Z.of_nat i))); [reflexivity|].
        rewrite wa_unsigned by lia. apply HOut; [lia|].
        destruct Ec as [E|E]; [apply Nat.leb_nle in E | apply Nat.ltb_nlt in E]; lia.
    - cbn [cells_size csize Nat.add] in HW |- *. rewrite ?Nat.add_0_r in HW |- *.
      exact (wr_at_transport rsegs mm mm' AA (Z.of_nat N) HW WM).
  Qed.

  (* The local bytes are application memory (they are inside the window). *)
  Lemma app_loc_F : forall fr f spc j n w56 mc X J t, FK fr f spc j n w56 -> p <> 0 -> o <> 0 ->
    BV fr j n w56 mc X J -> 0 <= t <= 56 -> app_mem (A + t).
  Proof.
    intros fr f spc j n w56 mc X J t HK Hp0 Ho0 PI Ht. hide_sec.
    pose proof HA1 as (HA32 & HAlo & HAhi). pose proof (zr_word sp) as Rsp. unfold inr64 in Rsp.
    pose proof HHM as HHM'. pose proof HAE as HAE'.
    unfold HIGHMEM_BEG, APPMEM_END in HHM', HAE'.
    unfold app_mem, LOWMEM_END, HIGHMEM_BEG, APPMEM_END. right.
    clear -HHM' HAE' HAlo HAhi Ht Rsp; lia.
  Qed.

  (* --- the calls the body makes, in footprint form --- *)

  (* __asan_memset(o + k, v, n): the box bytes [k, k + n) become v. *)
  Lemma cl_ms_F : forall fr f spc j n w56 mc X J (ret : Z) (kk nn : nat) (v : Z)
      (a0 a1 a2 t0 t1 t2 a3 a4 a5 a6 a7 s5' s6' s10' s11' t3 t4 t5 t6 : word),
    FK fr f spc j n w56 -> p <> 0 -> o <> 0 -> BV fr j n w56 mc X J ->
    ret_pc (Z_to_bv 64 ret) = Z_to_bv 64 ret -> (kk + nn <= 32)%nat -> (1 <= nn)%nat -> (kk + 7 <= 32)%nat ->
    0 <= v < 256 ->
    bv_unsigned a0 = o + Z.of_nat kk -> bv_unsigned a1 = v -> bv_unsigned a2 = Z.of_nat nn ->
    (forall (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (mc' : word -> option byte),
       BV fr j n w56 mc' (upd_bytes X kk (repeat (Z_to_bv 8 v) nn)) J ->
       evtF rsegs RNG (Q fr f spc j n w56) (MS (RB f fr (Z_to_bv 64 ret) (Z_to_bv 64 spc) t0' t1' t2' a0 a1' a2' a3' a4' a5' a6' a7'
                            s5' s6' s10' s11' t3' t4' t5' t6')
                        F (Z_to_bv 64 ret) fc None mc' (seg_rom rsegs))) ->
    evtF rsegs RNG (Q fr f spc j n w56) (MS (RB f fr (Z_to_bv 64 ret) (Z_to_bv 64 spc) t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7
                         s5' s6' s10' s11' t3 t4 t5 t6)
                     F (Z_to_bv 64 ASAN_MEMSET) fc None mc (seg_rom rsegs)).
  Proof.
    intros fr f spc j n w56 mc X J ret kk nn v a0 a1 a2 t0 t1 t2 a3 a4 a5 a6 a7 s5' s6' s10' s11' t3 t4 t5 t6
      HK Hp0 Ho0 PI Hret Hkn Hn Hk7 Hv E0 E1 E2 K.
    hide_sec.
    pose proof HA1 as (HA32 & HAlo & HAhi). pose proof (zr_word sp) as Rsp. unfold inr64 in Rsp.
    pose proof HHM as HHM'. pose proof HAE as HAE'.
    pose proof (spc_bounds fr f spc j n w56 HK) as HSPC.
    (* tauto on CF alone; the full-context tauto of the original used RP RPs RN RNs, so they are mentioned here
       to keep the closed type of cl_ms_F (its section variables) the same. *)
    pose proof (RP, RPs, RN, RNs) as _.
    assert (CFR : fr = spc \/ fr + 64 <= bv_unsigned sp - 4272)
      by (pose proof (call_facts fr f spc j n w56 mc X J HK Hp0 Ho0 PI) as CF; clear -CF; tauto).
    destruct (djw fr f spc j n w56 HK Hp0 Ho0) as (Dow & Dpo & Dpw & Dnm & Dfs & Dfr & Lrow & Boe & Bpe).
    destruct (fk_facts fr f spc j n w56 HK) as (FR8 & FRlo & FRhi & Fsp & FW & FAP & FRA & SW & SH1 & SH2).
    pose proof (bv_jx fr f spc j n w56 mc X J HK Hp0 Ho0 PI) as (JAC & JSW & JST & JAO & JAP & JAL & JAN & JJ1 & JJ2).
    pose proof PI as ((MU & WM & RM & MI & SV & (hh & HH) & F56) & HO32 & HL & HRB & HNB).
    pose proof FP0 as (DT0 & TS0 & C0 & T0 & DB0 & k0 & _ & _ & HPl0 & _ & _ & _ & HFSb & _ & _ & _).
    pose proof HPl0 as (P1 & P2 & P3 & P4 & P5). unfold FS_SIZE in P4, HFSb.
    unfold HIGHMEM_BEG, APPMEM_END in HHM', HAE'.
    assert (Rspc : 0 <= spc < 2 ^ 64) by (clear -HSPC HAlo HAhi Rsp HHM'; lia).
    pose proof (rs_rw_sub rsegs mc o 32 X kk nn HO32 Hkn) as HSub.
    destruct (stk_split rsegs mc (bv_unsigned sp - 4272) spc (bv_unsigned sp) JST ltac:(lia)) as [STlo _].
    unfold BINV.RB.
    eapply evtF_cut.
    { eapply HMSF with (lo := bv_unsigned sp - 4272) (junk := firstn nn (skipn kk X));
        unfold ASAN_MEMSET_K; rewrite ?E0, ?E1, ?E2, ?Nat2Z.id, ?(unsigned_lit spc) by exact Rspc.
      - exact HSub.
      - lia.
      - apply (B.acl_addr_sub mc o 32); [exact JAO | lia | lia | lia].
      - unfold end_in_app. right. replace (o + Z.of_nat kk + Z.of_nat nn) with (o + Z.of_nat (kk + nn)) by lia.
        apply app_o; [exact Ho0 | lia].
      - right. replace (o + Z.of_nat kk + 7) with (o + (Z.of_nat kk + 7)) by lia.
        apply app_o; [exact Ho0 | lia].
      - destruct (AO Ho0) as (_ & _ & DRT). unfold RT_LO, RT_HI in *. clear -DRT Hkn Hn; lia.
      - clear -Dow HSPC HAlo HAhi Hkn Hn; lia.
      - exact STlo.
      - clear -HSPC HAlo HAhi; lia.
      - unfold HIGHMEM_BEG; clear -HHM'; lia.
      - unfold APPMEM_END; clear -HSPC HAlo HAhi HAE'; lia.
      - exact JAC.
      - eapply A.ShadowRwOn.shadow_rw_on_mono;
          [ | exact (shadow_rw_on_mono_mem _ m mc SR0 WM RM) ];
        intros aa Haa;
        unfold asan_memset_c_on.asan_memset_shadow_R in Haa; rewrite ?E0, ?E2, ?Nat2Z.id in Haa;
        exact (box_shadow_sub aa kk nn Ho0 Hkn Hn Haa).
      - exact MI.
      - exact Rby.
      - eapply rng_sub; [exact Rimg | unfold IMG_LO; lia | unfold IMG_LO, IMG_HI; lia].
      - eapply rng_sub; [exact Rwin | unfold REAC_BOX_MODEL_BLOCK_K; lia | unfold REAC_BOX_MODEL_BLOCK_K; lia].
      - eapply rng_sub; [exact (RO Ho0) | lia | lia].
      - apply shw_ms_of_shc; [lia|]. eapply shc_sub; [exact (ROs Ho0) | lia | lia | lia].
      - apply shw_ms_of_shc; [lia|].
        eapply shc_sub; [exact Rwsh | unfold REAC_BOX_MODEL_BLOCK_K; lia | lia | unfold REAC_BOX_MODEL_BLOCK_K; lia].
      }
    intros ms' PO.
    destruct PO as (u0 & u1 & u2 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & m2 & Ems & MU2 & WM2 & MI2
                    & ST2 & RW2 & AC2 & SW2).
    subst ms'. rewrite ?(unsigned_lit spc) in MU2, ST2 by exact Rspc. rewrite E0, E1, E2, Nat2Z.id in RW2. rewrite E0, E2 in MU2.
    rewrite Z.mod_small in RW2 by lia.
    unfold ASAN_MEMSET_K in MU2, ST2.
    rewrite Hret.
    apply K.
    (* the invariant at the memory after the call *)
    assert (OUTC : forall x, (x < o + Z.of_nat kk \/ o + Z.of_nat kk + Z.of_nat nn <= x) ->
              (x < bv_unsigned sp - 4272 \/ bv_unsigned sp <= x) \/ (o <= x < o + 32) ->
              outside [(o + Z.of_nat kk, o + Z.of_nat kk + Z.of_nat nn); (spc - 2208, spc)] x).
    { intros x Hx1 Hx2. cbn [outside]. split; [lia|]. split; [|exact I].
      destruct Hx2 as [Hw|Hb]; [clear -Hw HSPC HAlo HAhi HHM'; lia | clear -Hb Dow HSPC HAlo HAhi; lia]. }
    assert (RM2 : rd_mono mc m2).
    { apply (B.rd_mono_list _ _ _ MU2). repeat constructor; cbn [fst snd]; intros y Hy.
      - apply (B.rd_of_bytes m2 _ _ (rw1 m2 _ _ _ RW2)).
        rewrite repeat_length. clear -Hy; lia.
      - apply (B.rd_of_stk m2 _ _ ST2). clear -Hy HSPC HAlo HAhi HHM'; lia. }
    split; [split; [|split; [|split; [|split; [|split; [|split]]]]]|].
    - apply (munch_trans _ m mc m2 MU).
      eapply munch_weaken; [|exact MU2]. unfold sub_fp. intros x Hx.
      unfold B.EBW in Hx.
      assert (Ebox : (p =? 0) || (o =? 0) = false)
        by (apply orb_false_iff; split; apply Z.eqb_neq; assumption).
      rewrite Ebox in Hx. apply B.out_appinv in Hx. destruct Hx as [Hw Hb].
      unfold B.Wf in Hw. cbn [outside] in Hw, Hb. destruct Hb as [Hb _].
      destruct Hw as (Hwin & _). cbn [outside]. split; [clear -Hb Hkn Hn; lia|].
      split; [clear -Hwin HSPC HAlo HAhi; lia | exact I].
    - exact (wmono_trans rsegs m mc m2 WM WM2).
    - exact (B.rd_mono_trans m mc m2 RM RM2).
    - exact MI2.
    - apply (rw_cells_transport rsegs _ mc m2 _ _ SV MU2 WM2).
      cbn [disjoint_from cells_size csize Nat.add B.SAVES].
      split; [clear -Dow HSPC HAlo HAhi Hkn Hn; lia|]. split; [clear -HSPC HAlo HAhi; lia | exact I].
    - exists hh. apply (bytes_at_transport rsegs _ mc m2 _ _ HH MU2).
      cbn [disjoint_from]. rewrite length_le8.
      split; [clear -Dfs Hkn Hn; lia|]. split; [clear -HFSb HHM' HSPC HAlo HAhi P1; lia | exact I].
    - apply (bytes_at_transport rsegs _ mc m2 _ _ F56 MU2).
      cbn [disjoint_from]. rewrite length_le8.
      split; [clear -Dfr Hkn Hn; lia|]. split; [clear -CFR HSPC HAlo HAhi; lia | exact I].
    - split; [|split; [|split]].
      + apply (rw_upd2_F mc m2 o 32 kk nn X (repeat (Z_to_bv 8 v) nn)
                 [(o + Z.of_nat kk, o + Z.of_nat kk + Z.of_nat nn); (spc - 2208, spc)] HO32 Hkn
                 ltac:(apply repeat_length) MU2 WM2).
        * intros x Hx Hx2. apply OUTC; [clear -Hx2; lia | right; clear -Hx; lia].
        * exact (rw1 m2 _ _ _ RW2).
      + apply (rw_cells_transport rsegs _ mc m2 _ _ HL MU2 WM2).
        cbn [disjoint_from cells_size csize Nat.add].
        split; [clear -Dow HSPC HAlo HAhi Hkn Hn; lia|]. split; [clear -HSPC HAlo HAhi; lia | exact I].
      + apply (bytes_at_transport rsegs _ mc m2 _ _ HRB MU2).
        cbn [disjoint_from]. rewrite Lrow.
        split; [clear -Dpo Hkn Hn; lia|]. split; [clear -Dpw HSPC HAlo HAhi; lia | exact I].
      + intros B5 H1 H2. destruct (Dnm B5 H1 H2) as (Dno & Dnw).
        apply (bytes_at_transport rsegs _ mc m2 _ _ (HNB B5 H1 H2) MU2).
        cbn [disjoint_from].
        split; [clear -Dno Hkn Hn; lia|]. split; [clear -Dnw HSPC HAlo HAhi; lia | exact I].
  Qed.


  (* __asan_memcpy(o + k, S, n): the box bytes [k, k + n) become src. *)
  Lemma cl_mc_F : forall fr f spc j n w56 mc X J (ret : Z) (kk nn : nat) (SS : Z) (src : list byte)
      (a0 a1 a2 t0 t1 t2 a3 a4 a5 a6 a7 s5' s6' s10' s11' t3 t4 t5 t6 : word),
    FK fr f spc j n w56 -> p <> 0 -> o <> 0 -> BV fr j n w56 mc X J ->
    ret_pc (Z_to_bv 64 ret) = Z_to_bv 64 ret -> (kk + nn <= 32)%nat -> (1 <= nn)%nat -> (kk + 7 <= 32)%nat ->
    length src = nn ->
    bv_unsigned a0 = o + Z.of_nat kk -> bv_unsigned a1 = SS -> bv_unsigned a2 = Z.of_nat nn ->
    bytes_at rsegs mc SS src -> addressable mc SS (Z.of_nat nn) -> app_mem (SS + 7) -> app_mem (SS + Z.of_nat nn) ->
    (SS + Z.of_nat nn <= o + Z.of_nat kk \/ o + Z.of_nat kk + Z.of_nat nn <= SS) ->
    (SS + Z.of_nat nn <= bv_unsigned sp - 4272 \/ A <= SS) ->
    rng RNG SS (Z.of_nat nn) -> sh_cover RNG SS (Z.of_nat nn) ->
    (forall a, sh_word_on SS (Z.of_nat nn) a ->
       C_ON.reac_box_model_block_shadow_R (bv_unsigned sp) FS p b o row nb a) ->
    (forall (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (mc' : word -> option byte),
       BV fr j n w56 mc' (upd_bytes X kk src) J ->
       evtF rsegs RNG (Q fr f spc j n w56) (MS (RB f fr (Z_to_bv 64 ret) (Z_to_bv 64 spc) t0' t1' t2' a0 a1' a2' a3' a4' a5' a6' a7'
                            s5' s6' s10' s11' t3' t4' t5' t6')
                        F (Z_to_bv 64 ret) fc None mc' (seg_rom rsegs))) ->
    evtF rsegs RNG (Q fr f spc j n w56) (MS (RB f fr (Z_to_bv 64 ret) (Z_to_bv 64 spc) t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7
                         s5' s6' s10' s11' t3 t4 t5 t6)
                     F (Z_to_bv 64 ASAN_MEMCPY) fc None mc (seg_rom rsegs)).
  Proof.
    intros fr f spc j n w56 mc X J ret kk nn SS src a0 a1 a2 t0 t1 t2 a3 a4 a5 a6 a7 s5' s6' s10' s11' t3 t4 t5 t6
      HK Hp0 Ho0 PI Hret Hkn Hn Hk7 LS E0 E1 E2 HSb HAS HS7 HSN DSO DSW RSS RSSs RSSon K.
    hide_sec.
    pose proof HA1 as (HA32 & HAlo & HAhi). pose proof (zr_word sp) as Rsp. unfold inr64 in Rsp.
    pose proof HHM as HHM'. pose proof HAE as HAE'.
    pose proof (call_facts fr f spc j n w56 mc X J HK Hp0 Ho0 PI) as (CF1 & CF2 & CF3 & CF4 & CF5 & CF6 & CF7 & CF8).
    destruct (djw fr f spc j n w56 HK Hp0 Ho0) as (Dow & Dpo & Dpw & Dnm & Dfs & Dfr & Lrow & Boe & Bpe).
    destruct (fk_facts fr f spc j n w56 HK) as (FR8 & FRlo & FRhi & Fsp & FW & FAP & FRA & SW & SH1 & SH2).
    pose proof (bv_jx fr f spc j n w56 mc X J HK Hp0 Ho0 PI) as (JAC & JSW & JST & JAO & JAP & JAL & JAN & JJ1 & JJ2).
    pose proof PI as ((MU & WM & RM & MI & SV & (hh & HH) & F56) & HO32 & HL & HRB & HNB).
    pose proof FP0 as (DT0 & TS0 & C0 & T0 & DB0 & k0 & _ & _ & HPl0 & _ & _ & _ & HFSb & _ & _ & _).
    pose proof HPl0 as (P1 & P2 & P3 & P4 & P5). unfold FS_SIZE in P4, HFSb.
    unfold HIGHMEM_BEG, APPMEM_END in HHM', HAE'.
    assert (Rspc : 0 <= spc < 2 ^ 64) by (clear -CF1 CF3 HHM' Rsp; lia).
    pose proof (rs_rw_sub rsegs mc o 32 X kk nn HO32 Hkn) as HSub.
    destruct (stk_split rsegs mc (bv_unsigned sp - 4272) spc (bv_unsigned sp) JST ltac:(lia)) as [STlo _].
    unfold BINV.RB.
    eapply evtF_cut.
    { eapply HMCF with (lo := bv_unsigned sp - 4272) (junk := firstn nn (skipn kk X)) (src := src);
        unfold ASAN_MEMCPY_K; rewrite ?E0, ?E1, ?E2, ?Nat2Z.id, ?(unsigned_lit spc) by exact Rspc.
      - exact HSb.
      - exact LS.
      - exact HSub.
      - right. exact DSO.
      - lia.
      - exact HAS.
      - apply (B.acl_addr_sub mc o 32); [exact JAO | lia | lia | lia].
      - unfold end_in_app. right. exact HSN.
      - unfold end_in_app. right.
        replace (o + Z.of_nat kk + Z.of_nat nn) with (o + Z.of_nat (kk + nn)) by lia.
        apply app_o; [exact Ho0 | lia].
      - right. split; [exact HS7|].
        replace (o + Z.of_nat kk + 7) with (o + (Z.of_nat kk + 7)) by lia.
        apply app_o; [exact Ho0 | lia].
      - destruct (AO Ho0) as (_ & _ & DRT). unfold RT_LO, RT_HI in *. clear -DRT Hkn Hn; lia.
      - clear -Dow CF1 CF3 CF7 HAlo HAhi Hkn Hn; lia.
      - clear -DSW CF1 CF3 CF7 HAlo HAhi; lia.
      - exact STlo.
      - clear -CF3; lia.
      - unfold HIGHMEM_BEG; clear -HHM'; lia.
      - exact CF5.
      - exact JAC.
      - eapply A.ShadowRwOn.shadow_rw_on_mono;
          [ | exact (shadow_rw_on_mono_mem _ m mc SR0 WM RM) ];
        intros aa Haa;
        unfold asan_memcpy_c_on.asan_memcpy_shadow_R in Haa; rewrite ?E0, ?E1, ?E2, ?Nat2Z.id in Haa;
        destruct Haa as [Hsrc | Hdst];
        [ exact (RSSon aa Hsrc) | exact (box_shadow_sub aa kk nn Ho0 Hkn Hn Hdst) ].
      - exact MI.
      - exact Rby.
      - eapply rng_sub; [exact Rimg | unfold IMG_LO; lia | unfold IMG_LO, IMG_HI; lia].
      - eapply rng_sub; [exact Rwin | unfold REAC_BOX_MODEL_BLOCK_K; lia | unfold REAC_BOX_MODEL_BLOCK_K; lia].
      - eapply rng_sub; [exact (RO Ho0) | lia | lia].
      - exact RSS.
      - apply shw_mc_of_shc; [lia|]. eapply shc_sub; [exact (ROs Ho0) | lia | lia | lia].
      - apply shw_mc_of_shc; [lia|]. exact RSSs.
      - apply shw_mc_of_shc; [lia|].
        eapply shc_sub; [exact Rwsh | unfold REAC_BOX_MODEL_BLOCK_K; lia | lia | unfold REAC_BOX_MODEL_BLOCK_K; lia].
      }
    intros ms' PO.
    destruct PO as (u0 & u1 & u2 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & m2 & Ems & MU2 & WM2 & MI2
                    & ST2 & RW2 & SB2 & AC2 & SW2).
    subst ms'. rewrite ?(unsigned_lit spc) in MU2, ST2 by exact Rspc. rewrite E0, E2, Nat2Z.id in RW2. rewrite E0, E2 in MU2. unfold ASAN_MEMCPY_K in MU2, ST2.
    rewrite Hret. apply K.
    assert (RM2 : rd_mono mc m2).
    { apply (B.rd_mono_list _ _ _ MU2). repeat constructor; cbn [fst snd]; intros y Hy.
      - apply (B.rd_of_bytes m2 _ _ (rw1 m2 _ _ _ RW2)). rewrite LS. clear -Hy; lia.
      - apply (B.rd_of_stk m2 _ _ ST2). clear -Hy CF1 CF3 HHM'; lia. }
    split; [split; [|split; [|split; [|split; [|split; [|split]]]]]|].
    - apply (munch_trans _ m mc m2 MU).
      eapply munch_weaken; [|exact MU2]. unfold sub_fp. intros x Hx.
      unfold B.EBW in Hx.
      assert (Ebox : (p =? 0) || (o =? 0) = false)
        by (apply orb_false_iff; split; apply Z.eqb_neq; assumption).
      rewrite Ebox in Hx. apply B.out_appinv in Hx. destruct Hx as [Hw Hb].
      unfold B.Wf in Hw. cbn [outside] in Hw, Hb. destruct Hb as [Hb _]. destruct Hw as (Hwin & _).
      cbn [outside]. split; [clear -Hb Hkn Hn; lia|].
      split; [clear -Hwin CF1 CF3; lia | exact I].
    - exact (wmono_trans rsegs m mc m2 WM WM2).
    - exact (B.rd_mono_trans m mc m2 RM RM2).
    - exact MI2.
    - apply (rw_cells_transport rsegs _ mc m2 _ _ SV MU2 WM2).
      cbn [disjoint_from cells_size csize Nat.add B.SAVES].
      split; [clear -Dow CF1 CF3 CF7 HAlo HAhi Hkn Hn; lia|]. split; [clear -CF1 CF3; lia | exact I].
    - exists hh. apply (bytes_at_transport rsegs _ mc m2 _ _ HH MU2).
      cbn [disjoint_from]. rewrite length_le8.
      split; [clear -Dfs Hkn Hn; lia|]. split; [clear -HFSb HHM' CF1 CF3 P1; lia | exact I].
    - apply (bytes_at_transport rsegs _ mc m2 _ _ F56 MU2).
      cbn [disjoint_from]. rewrite length_le8.
      split; [clear -Dfr Hkn Hn; lia|].
      split; [clear -CF8 CF1 CF3 CF7 HAlo HAhi; lia | exact I].
    - split; [|split; [|split]].
      + apply (rw_upd2_F mc m2 o 32 kk nn X src
                 [(o + Z.of_nat kk, o + Z.of_nat kk + Z.of_nat nn); (spc - 2224, spc)] HO32 Hkn LS MU2 WM2).
        * intros x Hx Hx2. cbn [outside]. split; [clear -Hx2; lia|].
          split; [clear -Hx Dow CF1 CF3 CF7 HAlo HAhi; lia | exact I].
        * exact (rw1 m2 _ _ _ RW2).
      + apply (rw_cells_transport rsegs _ mc m2 _ _ HL MU2 WM2).
        cbn [disjoint_from cells_size csize Nat.add].
        split; [clear -Dow CF1 CF3 CF7 HAlo HAhi Hkn Hn; lia|]. split; [clear -CF1 CF3 CF7; lia | exact I].
      + apply (bytes_at_transport rsegs _ mc m2 _ _ HRB MU2).
        cbn [disjoint_from]. rewrite Lrow.
        split; [clear -Dpo Hkn Hn; lia|]. split; [clear -Dpw CF1 CF3; lia | exact I].
      + intros B5 H1 H2. destruct (Dnm B5 H1 H2) as (Dno & Dnw).
        apply (bytes_at_transport rsegs _ mc m2 _ _ (HNB B5 H1 H2) MU2).
        cbn [disjoint_from].
        split; [clear -Dno Hkn Hn; lia|]. split; [clear -Dnw CF1 CF3; lia | exact I].
  Qed.


  (* __asan_memset(A + d, v, n): the local bytes [d, d + n) become v. *)
  Lemma cl_ms_loc_F : forall fr f spc j n w56 mc X J (ret : Z) (dd nn : nat) (v : Z)
      (a0 a1 a2 t0 t1 t2 a3 a4 a5 a6 a7 s5' s6' s10' s11' t3 t4 t5 t6 : word),
    FK fr f spc j n w56 -> p <> 0 -> o <> 0 -> BV fr j n w56 mc X J ->
    ret_pc (Z_to_bv 64 ret) = Z_to_bv 64 ret -> (dd + nn <= 56)%nat -> (1 <= nn)%nat -> (dd + 7 <= 56)%nat ->
    0 <= v < 256 ->
    bv_unsigned a0 = A + Z.of_nat dd -> bv_unsigned a1 = v -> bv_unsigned a2 = Z.of_nat nn ->
    (forall (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (mc' : word -> option byte),
       BV fr j n w56 mc' X (upd_bytes J dd (repeat (Z_to_bv 8 v) nn)) ->
       evtF rsegs RNG (Q fr f spc j n w56) (MS (RB f fr (Z_to_bv 64 ret) (Z_to_bv 64 spc) t0' t1' t2' a0 a1' a2' a3' a4' a5' a6' a7'
                            s5' s6' s10' s11' t3' t4' t5' t6')
                        F (Z_to_bv 64 ret) fc None mc' (seg_rom rsegs))) ->
    evtF rsegs RNG (Q fr f spc j n w56) (MS (RB f fr (Z_to_bv 64 ret) (Z_to_bv 64 spc) t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7
                         s5' s6' s10' s11' t3 t4 t5 t6)
                     F (Z_to_bv 64 ASAN_MEMSET) fc None mc (seg_rom rsegs)).
  Proof.
    intros fr f spc j n w56 mc X J ret dd nn v a0 a1 a2 t0 t1 t2 a3 a4 a5 a6 a7 s5' s6' s10' s11' t3 t4 t5 t6
      HK Hp0 Ho0 PI Hret Hdn Hn Hd7 Hv E0 E1 E2 K.
    hide_sec.
    pose proof HA1 as (HA32 & HAlo & HAhi). pose proof (zr_word sp) as Rsp. unfold inr64 in Rsp.
    pose proof HHM as HHM'. pose proof HAE as HAE'.
    pose proof (call_facts fr f spc j n w56 mc X J HK Hp0 Ho0 PI) as (CF1 & CF2 & CF3 & CF4 & CF5 & CF6 & CF7 & CF8).
    destruct (djw fr f spc j n w56 HK Hp0 Ho0) as (Dow & Dpo & Dpw & Dnm & Dfs & Dfr & Lrow & Boe & Bpe).
    destruct (fk_facts fr f spc j n w56 HK) as (FR8 & FRlo & FRhi & Fsp & FW & FAP & FRA & SW & SH1 & SH2).
    pose proof (bv_jx fr f spc j n w56 mc X J HK Hp0 Ho0 PI)
      as (JAC & JSW & JST & JAO & JAP & JAL & JAN & JJ1 & JJ2).
    pose proof (app_loc_F fr f spc j n w56 mc X J) as APL.
    pose proof PI as ((MU & WM & RM & MI & SV & (hh & HH) & F56) & HO32 & HL & HRB & HNB).
    pose proof FP0 as (DT0 & TS0 & C0 & T0 & DB0 & k0 & _ & _ & HPl0 & _ & _ & _ & HFSb & _ & _ & _).
    pose proof HPl0 as (P1 & P2 & P3 & P4 & P5). unfold FS_SIZE in P4, HFSb.
    unfold HIGHMEM_BEG, APPMEM_END in HHM', HAE'.
    assert (Rspc : 0 <= spc < 2 ^ 64) by (clear -CF1 CF3 HHM' Rsp; lia).
    pose proof (rs_rw_sub rsegs mc A 56 J dd nn HL Hdn) as HSub.
    destruct (stk_split rsegs mc (bv_unsigned sp - 4272) spc (bv_unsigned sp) JST ltac:(lia)) as [STlo _].
    unfold BINV.RB.
    eapply evtF_cut.
    { eapply HMSF with (lo := bv_unsigned sp - 4272) (junk := firstn nn (skipn dd J));
        unfold ASAN_MEMSET_K; rewrite ?E0, ?E1, ?E2, ?Nat2Z.id, ?(unsigned_lit spc) by exact Rspc.
      - exact HSub.
      - lia.
      - apply (B.acl_addr_sub mc A 56); [exact JAL | lia | lia | lia].
      - unfold end_in_app. right. replace (A + Z.of_nat dd + Z.of_nat nn) with (A + Z.of_nat (dd + nn)) by lia.
        apply (APL (Z.of_nat (dd + nn))); [exact HK | exact Hp0 | exact Ho0 | exact PI | lia].
      - right. replace (A + Z.of_nat dd + 7) with (A + (Z.of_nat dd + 7)) by lia.
        apply (APL (Z.of_nat dd + 7)); [exact HK | exact Hp0 | exact Ho0 | exact PI | lia].
      - unfold RT_LO, RT_HI. clear -HHM' HAlo HAhi Hdn; lia.
      - right. clear -CF7 HAlo HAhi; lia.
      - exact STlo.
      - clear -CF3; lia.
      - unfold HIGHMEM_BEG; clear -HHM'; lia.
      - exact CF5.
      - exact JAC.
      - eapply A.ShadowRwOn.shadow_rw_on_mono;
          [ | exact (shadow_rw_on_mono_mem _ m mc SR0 WM RM) ];
        intros aa Haa;
        unfold asan_memset_c_on.asan_memset_shadow_R in Haa; rewrite ?E0, ?E2, ?Nat2Z.id in Haa;
        refine (win_shadow_sub aa (A + Z.of_nat dd) (Z.of_nat nn) _ _ _ Haa);
        unfold REAC_BOX_MODEL_BLOCK_K; lia.
      - exact MI.
      - exact Rby.
      - eapply rng_sub; [exact Rimg | unfold IMG_LO; lia | unfold IMG_LO, IMG_HI; lia].
      - eapply rng_sub; [exact Rwin | unfold REAC_BOX_MODEL_BLOCK_K; lia | unfold REAC_BOX_MODEL_BLOCK_K; lia].
      - eapply rng_sub; [exact Rwin | unfold REAC_BOX_MODEL_BLOCK_K; lia | unfold REAC_BOX_MODEL_BLOCK_K; lia].
      - apply shw_ms_of_shc; [lia|].
        eapply shc_sub; [exact Rwsh | unfold REAC_BOX_MODEL_BLOCK_K; lia | lia | unfold REAC_BOX_MODEL_BLOCK_K; lia].
      - apply shw_ms_of_shc; [lia|].
        eapply shc_sub; [exact Rwsh | unfold REAC_BOX_MODEL_BLOCK_K; lia | lia | unfold REAC_BOX_MODEL_BLOCK_K; lia].
      }
    intros ms' PO.
    destruct PO as (u0 & u1 & u2 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & m2 & Ems & MU2 & WM2 & MI2
                    & ST2 & RW2 & AC2 & SW2).
    subst ms'. rewrite ?(unsigned_lit spc) in MU2, ST2 by exact Rspc. rewrite E0, E1, E2, Nat2Z.id in RW2. rewrite E0, E2 in MU2.
    rewrite Z.mod_small in RW2 by lia. unfold ASAN_MEMSET_K in MU2, ST2.
    rewrite Hret. apply K.
    assert (RM2 : rd_mono mc m2).
    { apply (B.rd_mono_list _ _ _ MU2). repeat constructor; cbn [fst snd]; intros y Hy.
      - apply (B.rd_of_bytes m2 _ _ (rw1 m2 _ _ _ RW2)). rewrite repeat_length. clear -Hy; lia.
      - apply (B.rd_of_stk m2 _ _ ST2). clear -Hy CF1 CF3 HHM'; lia. }
    split; [split; [|split; [|split; [|split; [|split; [|split]]]]]|].
    - apply (munch_trans _ m mc m2 MU).
      eapply munch_weaken; [|exact MU2]. unfold sub_fp. intros x Hx.
      unfold B.EBW in Hx. apply B.out_appinv in Hx. destruct Hx as [Hw _].
      unfold B.Wf in Hw. cbn [outside] in Hw. destruct Hw as (Hwin & _).
      cbn [outside]. split; [clear -Hwin CF1 CF3 CF7 HAlo HAhi Hdn; lia|].
      split; [clear -Hwin CF1 CF3; lia | exact I].
    - exact (wmono_trans rsegs m mc m2 WM WM2).
    - exact (B.rd_mono_trans m mc m2 RM RM2).
    - exact MI2.
    - apply (rw_cells_transport rsegs _ mc m2 _ _ SV MU2 WM2).
      cbn [disjoint_from cells_size csize Nat.add B.SAVES].
      split; [clear -CF6 CF7 HAlo HAhi Hdn; lia|]. split; [clear -CF1 CF3; lia | exact I].
    - exists hh. apply (bytes_at_transport rsegs _ mc m2 _ _ HH MU2).
      cbn [disjoint_from]. rewrite length_le8.
      split; [clear -HFSb HHM' CF1 CF3 CF7 HAlo HAhi P1 Hdn; lia|].
      split; [clear -HFSb HHM' CF1 CF3 P1; lia | exact I].
    - apply (bytes_at_transport rsegs _ mc m2 _ _ F56 MU2).
      cbn [disjoint_from]. rewrite length_le8.
      split; [clear -FRhi FRlo HAlo HAhi CF7 HFSb HHM' P1 Hdn; lia|].
      split; [clear -CF8 CF1 CF3 CF7 HAlo HAhi; lia | exact I].
    - split; [|split; [|split]].
      + apply (rw_cells_transport rsegs _ mc m2 _ _ HO32 MU2 WM2).
        cbn [disjoint_from cells_size csize Nat.add].
        split; [clear -Dow CF1 CF3 CF7 HAlo HAhi Hdn; lia|]. split; [clear -Dow CF1 CF3 CF7 HAlo HAhi; lia | exact I].
      + apply (rw_upd2_F mc m2 A 56 dd nn J (repeat (Z_to_bv 8 v) nn)
                 [(A + Z.of_nat dd, A + Z.of_nat dd + Z.of_nat nn); (spc - 2208, spc)] HL Hdn
                 ltac:(apply repeat_length) MU2 WM2).
        * intros x Hx Hx2. cbn [outside]. split; [clear -Hx2; lia|].
          split; [clear -Hx CF1 CF3 CF7 HAlo HAhi; lia | exact I].
        * exact (rw1 m2 _ _ _ RW2).
      + apply (bytes_at_transport rsegs _ mc m2 _ _ HRB MU2).
        cbn [disjoint_from]. rewrite Lrow.
        split; [clear -Dpw CF1 CF3 CF7 HAlo HAhi Hdn; lia|]. split; [clear -Dpw CF1 CF3; lia | exact I].
      + intros B5 H1 H2. destruct (Dnm B5 H1 H2) as (Dno & Dnw).
        apply (bytes_at_transport rsegs _ mc m2 _ _ (HNB B5 H1 H2) MU2).
        cbn [disjoint_from].
        split; [clear -Dnw CF1 CF3 CF7 HAlo HAhi Hdn; lia|]. split; [clear -Dnw CF1 CF3; lia | exact I].
  Qed.


  (* build_dt1_single(o, v, S, n) with the box all zeros: the box becomes dt1s v D. *)
  Lemma cl_bd_F : forall fr f spc j n w56 mc J (ret : Z) (nn : nat) (SS v : Z) (D : list byte)
      (a0 a1 a2 a3 t0 t1 t2 a4 a5 a6 a7 s5' s6' s10' s11' t3 t4 t5 t6 : word),
    FK fr f spc j n w56 -> p <> 0 -> o <> 0 -> BV fr j n w56 mc (zeros 32) J ->
    ret_pc (Z_to_bv 64 ret) = Z_to_bv 64 ret -> (nn <= 9)%nat -> (1 <= nn)%nat -> length D = nn ->
    bv_unsigned a0 = o -> bv_unsigned a1 = v -> bv_unsigned a2 = SS -> bv_unsigned a3 = Z.of_nat nn ->
    bytes_at rsegs mc SS D -> addressable mc SS (Z.of_nat nn) -> app_mem (SS + 7) ->
    app_mem (SS + Z.of_nat nn) ->
    (SS + Z.of_nat nn <= o \/ o + 32 <= SS) -> (A <= SS /\ SS + Z.of_nat nn <= A + 56) \/ (fr <= SS /\ SS + Z.of_nat nn <= fr + 64) ->
    rng RNG SS (Z.of_nat nn) -> sh_cover RNG SS (Z.of_nat nn) ->
    (forall a, sh_word_on SS (Z.of_nat nn) a ->
       C_ON.reac_box_model_block_shadow_R (bv_unsigned sp) FS p b o row nb a) ->
    (forall (t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (mc' : word -> option byte),
       BV fr j n w56 mc' (dt1s v D) J ->
       evtF rsegs RNG (Q fr f spc j n w56) (MS (RB f fr (Z_to_bv 64 ret) (Z_to_bv 64 spc) t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7'
                            s5' s6' s10' s11' t3' t4' t5' t6')
                        F (Z_to_bv 64 ret) fc None mc' (seg_rom rsegs))) ->
    evtF rsegs RNG (Q fr f spc j n w56) (MS (RB f fr (Z_to_bv 64 ret) (Z_to_bv 64 spc) t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7
                         s5' s6' s10' s11' t3 t4 t5 t6)
                     F (Z_to_bv 64 BUILD_DT1_SINGLE) fc None mc (seg_rom rsegs)).
  Proof.
    intros fr f spc j n w56 mc J ret nn SS v D a0 a1 a2 a3 t0 t1 t2 a4 a5 a6 a7 s5' s6' s10' s11' t3 t4 t5 t6
      HK Hp0 Ho0 PI Hret Hn9 Hn1 LD E0 E1 E2 E3 HSb HAS HS7 HSN DSO DSR RSS RSSs RSSon K.
    hide_sec.
    pose proof HA1 as (HA32 & HAlo & HAhi). pose proof (zr_word sp) as Rsp. unfold inr64 in Rsp.
    pose proof HHM as HHM'. pose proof HAE as HAE'.
    pose proof (call_facts fr f spc j n w56 mc (zeros 32) J HK Hp0 Ho0 PI)
      as (CF1 & CF2 & CF3 & CF4 & CF5 & CF6 & CF7 & CF8).
    destruct (djw fr f spc j n w56 HK Hp0 Ho0) as (Dow & Dpo & Dpw & Dnm & Dfs & Dfr & Lrow & Boe & Bpe).
    destruct (fk_facts fr f spc j n w56 HK) as (FR8 & FRlo & FRhi & Fsp & FW & FAP & FRA & SW & SH1 & SH2).
    pose proof (bv_jx fr f spc j n w56 mc (zeros 32) J HK Hp0 Ho0 PI)
      as (JAC & JSW & JST & JAO & JAP & JAL & JAN & JJ1 & JJ2).
    pose proof PI as ((MU & WM & RM & MI & SV & (hh & HH) & F56) & HO32 & HL & HRB & HNB).
    pose proof FP0 as (DT0 & TS0 & C0 & T0 & DB0 & k0 & _ & _ & HPl0 & _ & _ & _ & HFSb & _ & _ & _).
    pose proof HPl0 as (P1 & P2 & P3 & P4 & P5). unfold FS_SIZE in P4, HFSb.
    unfold HIGHMEM_BEG, APPMEM_END in HHM', HAE'.
    assert (Rspc : 0 <= spc < 2 ^ 64) by (clear -CF1 CF3 HHM' Rsp; lia).
    destruct (stk_split rsegs mc (bv_unsigned sp - 4272) spc (bv_unsigned sp) JST ltac:(lia)) as [STlo _].
    destruct (stk_split rsegs mc (bv_unsigned sp - 4272) (spc - 2272) spc STlo ltac:(clear -CF1 CF3; lia))
      as [_ STbd].
    unfold BINV.RB.
    eapply evtF_cut.
    { eapply HBDF with (ob := zeros 32) (D := D); unfold BUILD_DT1_SINGLE_K;
        rewrite ?E0, ?E1, ?E2, ?E3, ?Nat2Z.id, ?(unsigned_lit spc) by exact Rspc.
      - exact STbd.
      - lia.
      - exact Ho0.
      - unfold APPMEM_END in Boe; clear -Boe; lia.
      - exact HO32.
      - clear -HSN HAS; destruct HAS as (_ & _ & He & _); unfold APPMEM_END in He; lia.
      - rewrite LD. reflexivity.
      - exact HSb.
      - exact DSO.
      - clear -Dow CF1 CF3 CF7 HAlo HAhi; lia.
      - clear -DSR CF1 CF3 CF7 CF8; lia.
      - exact MI.
      - exact JAC.
      - eapply A.ShadowRwOn.shadow_rw_on_mono;
          [ | exact (shadow_rw_on_mono_mem _ m mc SR0 WM RM) ];
        intros aa Haa;
        unfold build_dt1_single_shadow_R in Haa; rewrite ?E0, ?E2, ?E3, ?Nat2Z.id in Haa;
        destruct Haa as [Hsrc | Hdst];
        [ exact (RSSon aa Hsrc)
        | exact (box_shadow_sub aa 20%nat nn Ho0 ltac:(lia) ltac:(lia) Hdst) ].
      - unfold HIGHMEM_BEG; clear -HHM' CF1 CF3; lia.
      - exact CF5.
      - exact JAO.
      - exact HAS.
      - replace (o + 32) with (o + 32) by reflexivity. apply app_o; [exact Ho0 | lia].
      - unfold end_in_app. right. exact HSN.
      - right. exact HS7.
      - destruct (AO Ho0) as (_ & _ & DRT). exact DRT.
      - exact Rby.
      - eapply rng_sub; [exact Rimg | unfold IMG_LO; lia | unfold IMG_LO, IMG_HI; lia].
      - eapply rng_sub; [exact Rwin | unfold REAC_BOX_MODEL_BLOCK_K; lia | unfold REAC_BOX_MODEL_BLOCK_K; lia].
      - apply shw_mc_of_shc; [lia|].
        eapply shc_sub; [exact Rwsh | unfold REAC_BOX_MODEL_BLOCK_K; lia | lia | unfold REAC_BOX_MODEL_BLOCK_K; lia].
      - eapply rng_sub; [exact Rimg | unfold RT_LO; lia | unfold RT_LO, RT_HI, IMG_LO; lia].
      - exact (RO Ho0).
      - pose proof (ROs Ho0) as RBO. unfold sh_cover, shadow_addr in RBO.
        replace (o + 32 - 1) with (o + 31) in RBO by lia. exact RBO.
      - exact RSS.
      - right. pose proof RSSs as RBS. unfold sh_cover, shadow_addr in RBS. exact RBS.
      }
    intros ms' PO.
    destruct PO as (u0 & u1 & u2 & x10 & x11 & x12 & x13 & x14 & x15 & x16 & x17 & u3 & u4 & u5 & u6 & m2 & Ems
                    & HB2 & _ & _ & MU2 & WM2 & MI2 & ST2 & AC2 & SW2).
    subst ms'. rewrite ?(unsigned_lit spc) in MU2, ST2 by exact Rspc. rewrite E0, E1, E3, Nat2Z.id in HB2. rewrite E0, E3 in MU2. unfold BUILD_DT1_SINGLE_K in MU2, ST2.
    rewrite Hret. apply K.
    assert (LDT : length (dt1s v D) = 32%nat) by (apply rs_dt1s_len; lia).
    assert (EDT : dt1_out nn v D (zeros 32) = dt1s v D) by (unfold dt1s; rewrite LD; reflexivity).
    rewrite EDT in HB2.
    assert (OUTC : forall x, (x < o \/ o + 32 <= x) -> (x < bv_unsigned sp - 4272 \/ bv_unsigned sp <= x) ->
              outside [(spc - 2272, spc); (o, o + 22 + Z.of_nat nn); (o + 31, o + 32)] x).
    { intros x H1 H2. cbn [outside]. split; [clear -H2 CF1 CF3; lia|].
      split; [clear -H1 Hn9; lia|]. split; [clear -H1; lia | exact I]. }
    assert (RM2 : rd_mono mc m2).
    { apply (B.rd_mono_list _ _ _ MU2). repeat constructor; cbn [fst snd]; intros y Hy.
      - apply (B.rd_of_stk m2 _ _ ST2). clear -Hy CF1 CF3 HHM'; lia.
      - apply (B.rd_of_bytes m2 _ _ HB2). rewrite LDT. clear -Hy Hn9; lia.
      - apply (B.rd_of_bytes m2 _ _ HB2). rewrite LDT. clear -Hy; lia. }
    split; [split; [|split; [|split; [|split; [|split; [|split]]]]]|].
    - apply (munch_trans _ m mc m2 MU).
      eapply munch_weaken; [|exact MU2]. unfold sub_fp. intros x Hx.
      unfold B.EBW in Hx.
      assert (Ebox : (p =? 0) || (o =? 0) = false)
        by (apply orb_false_iff; split; apply Z.eqb_neq; assumption).
      rewrite Ebox in Hx. apply B.out_appinv in Hx. destruct Hx as [Hw Hb].
      unfold B.Wf in Hw. cbn [outside] in Hw, Hb. destruct Hb as [Hb _]. destruct Hw as (Hwin & _).
      cbn [outside]. split; [clear -Hwin CF1 CF3; lia|].
      split; [clear -Hb Hn9; lia|]. split; [clear -Hb; lia | exact I].
    - exact (wmono_trans rsegs m mc m2 WM WM2).
    - exact (B.rd_mono_trans m mc m2 RM RM2).
    - exact MI2.
    - apply (rw_cells_transport rsegs _ mc m2 _ _ SV MU2 WM2).
      cbn [disjoint_from cells_size csize Nat.add B.SAVES].
      split; [clear -CF1 CF3; lia|]. split; [clear -Dow CF1 CF3 CF7 HAlo HAhi Hn9; lia|].
      split; [clear -Dow CF1 CF3 CF7 HAlo HAhi; lia | exact I].
    - exists hh. apply (bytes_at_transport rsegs _ mc m2 _ _ HH MU2).
      cbn [disjoint_from]. rewrite length_le8.
      split; [clear -HFSb HHM' CF1 CF3 P1; lia|].
      split; [clear -Dfs Hn9; lia|]. split; [clear -Dfs; lia | exact I].
    - apply (bytes_at_transport rsegs _ mc m2 _ _ F56 MU2).
      cbn [disjoint_from]. rewrite length_le8.
      split; [clear -CF8 CF1 CF3 CF7 HAlo HAhi; lia|].
      split; [clear -Dfr Hn9; lia|]. split; [clear -Dfr; lia | exact I].
    - split; [|split; [|split]].
      + pose proof HO32 as [_ WO]. cbn [cells_size csize Nat.add] in WO.
        split; [split|].
        * cbn [cells_wf cell_wf]. split; [exact LDT | exact I].
        * cbn [cells_bytes cbytes]. rewrite app_nil_r. exact HB2.
        * cbn [cells_size csize Nat.add]. exact (wr_at_transport rsegs mc m2 o (Z.of_nat 32) WO WM2).
      + apply (rw_cells_transport rsegs _ mc m2 _ _ HL MU2 WM2).
        cbn [disjoint_from cells_size csize Nat.add].
        split; [clear -CF1 CF3 CF7; lia|].
        split; [clear -Dow CF1 CF3 CF7 HAlo HAhi Hn9; lia|]. split; [clear -Dow CF1 CF3 CF7 HAlo HAhi; lia | exact I].
      + apply (bytes_at_transport rsegs _ mc m2 _ _ HRB MU2).
        cbn [disjoint_from]. rewrite Lrow.
        split; [clear -Dpw CF1 CF3; lia|]. split; [clear -Dpo Hn9; lia|]. split; [clear -Dpo; lia | exact I].
      + intros B5 H1 H2. destruct (Dnm B5 H1 H2) as (Dno & Dnw).
        apply (bytes_at_transport rsegs _ mc m2 _ _ (HNB B5 H1 H2) MU2).
        cbn [disjoint_from].
        split; [clear -Dnw CF1 CF3; lia|]. split; [clear -Dno Hn9; lia|]. split; [clear -Dno; lia | exact I].
  Qed.


End MainF.

(* --------------------------------------------------------------------------------------------------------- *)
(* The corollaries: the original Exec.evt statements of reac_box_model_block_binv2.v re-derived from the footprint
   forms with ExecF.RNG_all, the post Q := Q0 and the continuation HKR := reac_box_model_block_epiF.bmb_KR_Q0.
   This is the check that each _F statement is the old one plus footprint premises, nothing weaker. The callee
   contract stays in its _F form (a run that calls __asan_memset cannot be re-played without the callee's
   footprint contract), and so does the lemma's own continuation premise, for the same reason.
   Text of the section and of all_rng: reac_box_model_block_epiF.v:879-950. *)
Section OfF.
  Variables (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (m : word -> option byte) (p b o FS off A : Z) (row nb ob : list byte).
  Hypothesis HMSF : asan_memset_cF_on.asan_memset_contract_F_on.
  Hypothesis HMCF : asan_memcpy_cF_on.asan_memcpy_contract_F_on.
  Hypothesis HBDF : build_dt1_single_contract_F_on.
  Hypothesis Hoff : off = ASAN_K.
  Hypothesis HA : A = (bv_unsigned sp - 160) / 32 * 32.
  Hypothesis HS16 : bv_unsigned sp mod 16 = 0.
  Hypothesis ST0 : stk rsegs m (bv_unsigned sp - 4272) (bv_unsigned sp).
  Hypothesis MI0 : mem_inv rsegs m.
  Hypothesis AC0 : asan_cells m.
  (* The corollaries keep the WIDE premise and narrow it on the spot, so the statement they re-derive is the
     proved file's: the Let keeps the name SR0, so inst_exact of the _F lemmas still instantiates it
     (pattern of reac_box_model_block_cF_on.v:99-116 and of reac_box_model_block_epiF.v's Section OfF). *)
  Hypothesis SRW : shadow_rw m.
  Let SR0 : A.ShadowRwOn.shadow_rw_on (C_ON.reac_box_model_block_shadow_R (bv_unsigned sp) FS p b o row nb) m :=
    A.ShadowRwOn.shadow_rw_on_of_shadow_rw _ m SRW.
  Hypothesis HHM : HIGHMEM_BEG <= bv_unsigned sp - 4272.
  Hypothesis HAE : bv_unsigned sp <= APPMEM_END.
  Hypothesis AW0 : addressable m (bv_unsigned sp - 4272) 4272.
  Hypothesis FP0 : fp [0%nat] m (bv_unsigned tp) FS (bv_unsigned sp - 4272) (bv_unsigned sp)
    (reac_box_model_block_W o (bv_unsigned sp)) (reac_box_model_block_D p o).
  Hypothesis TLS0 : reac_box_model_block_tls m (bv_unsigned tp) FS (bv_unsigned sp - REAC_BOX_MODEL_BLOCK_K) (bv_unsigned sp).
  Hypothesis Rp : 0 <= p < 2^64.
  Hypothesis Rb : 0 <= b < 2^64.
  Hypothesis Ro : 0 <= o < 2^64.
  Hypothesis HP : p <> 0 -> p mod 8 = 0 /\ length row = 296%nat /\ bytes_at rsegs m p row /\
    (bv_unsigned sp <= p \/ p + 296 <= bv_unsigned sp - 4272) /\ (o = 0 \/ o + 32 <= p \/ p + 296 <= o).
  Hypothesis HN : p <> 0 -> (b = 5 \/ b = 6) -> has row <> 0 -> rname row <> 0 ->
    name_ok nb /\ bytes_at rsegs m (rname row) nb /\
    (bv_unsigned sp <= rname row \/ rname row + Z.of_nat (length nb) <= bv_unsigned sp - 4272) /\
    (o = 0 \/ o + 32 <= rname row \/ rname row + Z.of_nat (length nb) <= o).
  Hypothesis HO : o <> 0 -> rw_cells rsegs m o [CB 32 ob] /\
    (bv_unsigned sp <= o \/ o + 32 <= bv_unsigned sp - 4272) /\ (o + 32 <= JOIN_0013 \/ JOIN_0014 + 32 <= o).
  Hypothesis AP : p <> 0 -> addressable m p 296.
  Hypothesis ANB : p <> 0 -> (b = 5 \/ b = 6) -> has row <> 0 -> rname row <> 0 ->
    addressable m (rname row) (Z.of_nat (length nb)).
  Hypothesis AO : o <> 0 -> addressable m o 32 /\ app_mem (o + 32) /\ (o + 32 <= RT_LO \/ RT_HI <= o).
  Hypothesis AJ1 : b = 1 -> addressable m JOIN_0014 32.
  Hypothesis AJ2 : b = 2 -> addressable m JOIN_0013 32.
  Hypothesis NDJ : p <> 0 -> (b = 5 \/ b = 6) -> has row <> 0 -> rname row <> 0 ->
    fp_dj [(rname row, rname row + Z.of_nat (length nb))] (fp_w [0%nat] FS).

  Notation FK := (B.FK FS A).
  Notation SAVES := (B.SAVES ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11).
  (* Route (C): the post of the family is a Theorem Labs lane's reac_box_model_block_post_on (reac_box_model_block_c_on.v:47), whose shadow
     conjunct is the region transport; a Theorem Labs lane's bmb_KR_Q0 concludes it. *)
  Notation Q0 := (C_ON.reac_box_model_block_post_on ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
                    F fc m p b o FS row nb).
  Notation BV := (BINVF.BV_F ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m p b o FS A row nb).
  Notation RB := (BINVF.RB_F sp gp tp p o off A).

  (* The footprint forms at this section's variables, still waiting for RNG, its region premises, Q and HKR. *)
  Let cl_ms_F0 := ltac2:(inst_exact @cl_ms_F).
  Let cl_mc_F0 := ltac2:(inst_exact @cl_mc_F).
  Let cl_ms_loc_F0 := ltac2:(inst_exact @cl_ms_loc_F).
  Let cl_bd_F0 := ltac2:(inst_exact @cl_bd_F).
  Let bmb_KR_Q00 := ltac2:(inst_exact @BEPIF.bmb_KR_Q0).

  (* Section MainF's hide_sec at this section's hypotheses, the first tactic of every proof below: the lia of
     all_rng then does not search their disjunctions, implications and HA's division. *)
  Ltac hide_secO :=
    let hd H := let T := type of H in change (mb_hide T) in H in
    hd HP; hd HN; hd HO; hd AP; hd ANB; hd AO; hd AJ1; hd AJ2; hd NDJ; hd HA; hd HS16.

  (* In the original each lemma below used all four footprint forms above (its closed type abstracts all three
     callee contracts), and all_rng now clears them: each lemma mentions all four once, to keep its closed type. *)
  Ltac keep_F0 := pose proof (cl_ms_F0, cl_mc_F0, cl_ms_loc_F0, cl_bd_F0) as _.

  (* The all-footprint meets every region premise of this family's runs. *)
  Let FShi : FS + FS_SIZE <= 2^64.
  Proof.
    hide_secO.
    pose proof FP0 as (DT & TS & C & T & DB & k & _ & _ & HPl & _).
    pose proof HPl as (P1 & P2 & P3 & P4 & P5).
    pose proof (P4 (FS + FS_SIZE - 1) ltac:(unfold FS_SIZE; lia)) as A2.
    unfold app_mem, LOWMEM_END, HIGHMEM_BEG, APPMEM_END in A2. lia.
  Qed.

  Let FSlo : 0 <= FS.
  Proof.
    hide_secO.
    pose proof FP0 as (DT & TS & C & T & DB & k & _ & _ & HPl & _).
    pose proof HPl as (P1 & P2 & P3 & P4 & P5). lia.
  Qed.

  Ltac bounds0 :=
    repeat match goal with
    | H : addressable ?mm ?a ?n |- _ =>
        let AB := fresh "AB" in pose proof H as AB; destruct AB as (? & ? & ? & _);
        change (mb_hide (addressable mm a n)) in H
    end;
    repeat match goal with H : mb_hide (addressable _ _ _) |- _ => unfold mb_hide in H end;
    try (match goal with H : o <> 0 |- _ => destruct (AO H) as ((? & ? & ? & _) & ? & ?) end);
    try (match goal with H : p <> 0 |- _ => destruct (AP H) as (? & ? & ? & _) end);
    try (match goal with H1 : p <> 0, H2 : (b = 5 \/ b = 6), H3 : has row <> 0, H4 : rname row <> 0 |- _ =>
           destruct (ANB H1 H2 H3 H4) as (? & ? & ? & _) end);
    try (match goal with H : b = 1 |- _ => destruct (AJ1 H) as (? & ? & ? & _) end);
    try (match goal with H : b = 2 |- _ => destruct (AJ2 H) as (? & ? & ? & _) end);
    unfold HIGHMEM_BEG, APPMEM_END in *.

  Ltac all_rng :=
    (* No region goal needs the footprint forms or the epi continuation above, and the shadow covers in their
       types are divisions that Z.div_mod_to_equations below would generalize one by one. *)
    try clear cl_ms_F0; try clear cl_mc_F0; try clear cl_ms_loc_F0; try clear cl_bd_F0; try clear bmb_KR_Q00;
    let HHM' := fresh in let HAE' := fresh in
    pose proof HHM as HHM'; pose proof HAE as HAE';
    unfold HIGHMEM_BEG, APPMEM_END in *;
    unfold sh_cover, rng_asan.sh_word_rng, rng_asan.sh_al8_lo, rng_asan.sh_al8_hi,
           rng_ivls, reac_box_model_block_tls_rng, rng_bytes,
           shadow_addr, ASAN_K, REAC_BOX_MODEL_BLOCK_K, fs_frame, fs_flag, fs_hint, fs_M, fs_B, FS_SIZE in *;
    repeat (intros || split || apply Forall_cons || apply Forall_nil);
    try exact I;
    bounds0;
    try (apply ExecF.rng_all; cbn [Z.of_nat]; Z.div_mod_to_equations; lia);
    try (cbn [Z.of_nat]; Z.div_mod_to_equations; lia).

  (* The region bounds the all-footprint needs: 0 <= a and a + n <= APPMEM_END for each range the lemma names.
     They sit in the addressable premises of the lemma and in the section's AO / AP. *)
  (* The original cl_ms (reac_box_model_block_binv2.v:337), with the continuation premise in evtF form
     at ExecF.RNG_all: the lemma passes its continuation on, so the old evt continuation cannot be
     re-played by a footprint run. *)
  Lemma cl_ms_of_F : forall fr f spc j n w56 mc X J (ret : Z) (kk nn : nat) (v : Z)
      (a0 a1 a2 t0 t1 t2 a3 a4 a5 a6 a7 s5' s6' s10' s11' t3 t4 t5 t6 : word),
    FK fr f spc j n w56 -> p <> 0 -> o <> 0 -> BV fr j n w56 mc X J ->
    ret_pc (Z_to_bv 64 ret) = Z_to_bv 64 ret -> (kk + nn <= 32)%nat -> (1 <= nn)%nat -> (kk + 7 <= 32)%nat ->
    0 <= v < 256 ->
    bv_unsigned a0 = o + Z.of_nat kk -> bv_unsigned a1 = v -> bv_unsigned a2 = Z.of_nat nn ->
    (forall (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (mc' : word -> option byte),
       BV fr j n w56 mc' (upd_bytes X kk (repeat (Z_to_bv 8 v) nn)) J ->
       evtF rsegs ExecF.RNG_all Q0 (MS (RB f fr (Z_to_bv 64 ret) (Z_to_bv 64 spc) t0' t1' t2' a0 a1' a2' a3' a4' a5' a6' a7'
                            s5' s6' s10' s11' t3' t4' t5' t6')
                        F (Z_to_bv 64 ret) fc None mc' (seg_rom rsegs))) ->
    evt rsegs Q0 (MS (RB f fr (Z_to_bv 64 ret) (Z_to_bv 64 spc) t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7
                         s5' s6' s10' s11' t3 t4 t5 t6)
                     F (Z_to_bv 64 ASAN_MEMSET) fc None mc (seg_rom rsegs)).
  Proof.
    intros fr f spc j n w56 mc X J ret kk nn v a0 a1 a2 t0 t1 t2 a3 a4 a5 a6 a7 s5' s6' s10' s11' t3 t4 t5 t6
      HK Hp0 Ho0 PI Hret Hkn Hn Hk7 Hv E0 E1 E2 K.
    hide_secO. keep_F0. bounds0.
    apply (ExecF.evtF_evt rsegs ExecF.RNG_all).
    eapply cl_ms_F0 with (Q := fun _ _ _ _ _ _ => Q0) (fr := fr) (f := f) (spc := spc) (j := j) (n := n) (w56 := w56) (mc := mc) (X := X) (J := J)
      (ret := ret) (kk := kk) (nn := nn) (v := v);
      try eassumption; try assumption; try (apply bmb_KR_Q00; all_rng); all_rng.
  Qed.

  (* The original cl_mc (reac_box_model_block_binv2.v:451), with the continuation premise in evtF form
     at ExecF.RNG_all: the lemma passes its continuation on, so the old evt continuation cannot be
     re-played by a footprint run. *)
  Lemma cl_mc_of_F : forall fr f spc j n w56 mc X J (ret : Z) (kk nn : nat) (SS : Z) (src : list byte)
      (a0 a1 a2 t0 t1 t2 a3 a4 a5 a6 a7 s5' s6' s10' s11' t3 t4 t5 t6 : word),
    FK fr f spc j n w56 -> p <> 0 -> o <> 0 -> BV fr j n w56 mc X J ->
    ret_pc (Z_to_bv 64 ret) = Z_to_bv 64 ret -> (kk + nn <= 32)%nat -> (1 <= nn)%nat -> (kk + 7 <= 32)%nat ->
    length src = nn ->
    bv_unsigned a0 = o + Z.of_nat kk -> bv_unsigned a1 = SS -> bv_unsigned a2 = Z.of_nat nn ->
    bytes_at rsegs mc SS src -> addressable mc SS (Z.of_nat nn) -> app_mem (SS + 7) -> app_mem (SS + Z.of_nat nn) ->
    (SS + Z.of_nat nn <= o + Z.of_nat kk \/ o + Z.of_nat kk + Z.of_nat nn <= SS) ->
    (SS + Z.of_nat nn <= bv_unsigned sp - 4272 \/ A <= SS) ->
    (forall a, sh_word_on SS (Z.of_nat nn) a ->
       C_ON.reac_box_model_block_shadow_R (bv_unsigned sp) FS p b o row nb a) ->
    (forall (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (mc' : word -> option byte),
       BV fr j n w56 mc' (upd_bytes X kk src) J ->
       evtF rsegs ExecF.RNG_all Q0 (MS (RB f fr (Z_to_bv 64 ret) (Z_to_bv 64 spc) t0' t1' t2' a0 a1' a2' a3' a4' a5' a6' a7'
                            s5' s6' s10' s11' t3' t4' t5' t6')
                        F (Z_to_bv 64 ret) fc None mc' (seg_rom rsegs))) ->
    evt rsegs Q0 (MS (RB f fr (Z_to_bv 64 ret) (Z_to_bv 64 spc) t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7
                         s5' s6' s10' s11' t3 t4 t5 t6)
                     F (Z_to_bv 64 ASAN_MEMCPY) fc None mc (seg_rom rsegs)).
  Proof.
    intros fr f spc j n w56 mc X J ret kk nn SS src a0 a1 a2 t0 t1 t2 a3 a4 a5 a6 a7 s5' s6' s10' s11' t3 t4 t5 t6
      HK Hp0 Ho0 PI Hret Hkn Hn Hk7 LS E0 E1 E2 HSb HAS HS7 HSN DSO DSW RSSon K.
    hide_secO. keep_F0. bounds0.
    apply (ExecF.evtF_evt rsegs ExecF.RNG_all).
    eapply cl_mc_F0 with (Q := fun _ _ _ _ _ _ => Q0) (fr := fr) (f := f) (spc := spc) (j := j) (n := n) (w56 := w56) (mc := mc) (X := X) (J := J)
      (ret := ret) (kk := kk) (nn := nn) (SS := SS) (src := src);
      try eassumption; try assumption; try (apply bmb_KR_Q00; all_rng); all_rng.
  Qed.

  (* The original cl_ms_loc (reac_box_model_block_binv2.v:576), with the continuation premise in evtF form
     at ExecF.RNG_all: the lemma passes its continuation on, so the old evt continuation cannot be
     re-played by a footprint run. *)
  Lemma cl_ms_loc_of_F : forall fr f spc j n w56 mc X J (ret : Z) (dd nn : nat) (v : Z)
      (a0 a1 a2 t0 t1 t2 a3 a4 a5 a6 a7 s5' s6' s10' s11' t3 t4 t5 t6 : word),
    FK fr f spc j n w56 -> p <> 0 -> o <> 0 -> BV fr j n w56 mc X J ->
    ret_pc (Z_to_bv 64 ret) = Z_to_bv 64 ret -> (dd + nn <= 56)%nat -> (1 <= nn)%nat -> (dd + 7 <= 56)%nat ->
    0 <= v < 256 ->
    bv_unsigned a0 = A + Z.of_nat dd -> bv_unsigned a1 = v -> bv_unsigned a2 = Z.of_nat nn ->
    (forall (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (mc' : word -> option byte),
       BV fr j n w56 mc' X (upd_bytes J dd (repeat (Z_to_bv 8 v) nn)) ->
       evtF rsegs ExecF.RNG_all Q0 (MS (RB f fr (Z_to_bv 64 ret) (Z_to_bv 64 spc) t0' t1' t2' a0 a1' a2' a3' a4' a5' a6' a7'
                            s5' s6' s10' s11' t3' t4' t5' t6')
                        F (Z_to_bv 64 ret) fc None mc' (seg_rom rsegs))) ->
    evt rsegs Q0 (MS (RB f fr (Z_to_bv 64 ret) (Z_to_bv 64 spc) t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7
                         s5' s6' s10' s11' t3 t4 t5 t6)
                     F (Z_to_bv 64 ASAN_MEMSET) fc None mc (seg_rom rsegs)).
  Proof.
    intros fr f spc j n w56 mc X J ret dd nn v a0 a1 a2 t0 t1 t2 a3 a4 a5 a6 a7 s5' s6' s10' s11' t3 t4 t5 t6
      HK Hp0 Ho0 PI Hret Hdn Hn Hd7 Hv E0 E1 E2 K.
    hide_secO. keep_F0. bounds0.
    apply (ExecF.evtF_evt rsegs ExecF.RNG_all).
    eapply cl_ms_loc_F0 with (Q := fun _ _ _ _ _ _ => Q0) (fr := fr) (f := f) (spc := spc) (j := j) (n := n) (w56 := w56) (mc := mc) (X := X) (J := J)
      (ret := ret) (dd := dd) (nn := nn) (v := v);
      try eassumption; try assumption; try (apply bmb_KR_Q00; all_rng); all_rng.
  Qed.

  (* The original cl_bd (reac_box_model_block_binv2.v:680), with the continuation premise in evtF form
     at ExecF.RNG_all: the lemma passes its continuation on, so the old evt continuation cannot be
     re-played by a footprint run. *)
  Lemma cl_bd_of_F : forall fr f spc j n w56 mc J (ret : Z) (nn : nat) (SS v : Z) (D : list byte)
      (a0 a1 a2 a3 t0 t1 t2 a4 a5 a6 a7 s5' s6' s10' s11' t3 t4 t5 t6 : word),
    FK fr f spc j n w56 -> p <> 0 -> o <> 0 -> BV fr j n w56 mc (zeros 32) J ->
    ret_pc (Z_to_bv 64 ret) = Z_to_bv 64 ret -> (nn <= 9)%nat -> (1 <= nn)%nat -> length D = nn ->
    bv_unsigned a0 = o -> bv_unsigned a1 = v -> bv_unsigned a2 = SS -> bv_unsigned a3 = Z.of_nat nn ->
    bytes_at rsegs mc SS D -> addressable mc SS (Z.of_nat nn) -> app_mem (SS + 7) ->
    app_mem (SS + Z.of_nat nn) ->
    (SS + Z.of_nat nn <= o \/ o + 32 <= SS) -> (A <= SS /\ SS + Z.of_nat nn <= A + 56) \/ (fr <= SS /\ SS + Z.of_nat nn <= fr + 64) ->
    (forall a, sh_word_on SS (Z.of_nat nn) a ->
       C_ON.reac_box_model_block_shadow_R (bv_unsigned sp) FS p b o row nb a) ->
    (forall (t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (mc' : word -> option byte),
       BV fr j n w56 mc' (dt1s v D) J ->
       evtF rsegs ExecF.RNG_all Q0 (MS (RB f fr (Z_to_bv 64 ret) (Z_to_bv 64 spc) t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7'
                            s5' s6' s10' s11' t3' t4' t5' t6')
                        F (Z_to_bv 64 ret) fc None mc' (seg_rom rsegs))) ->
    evt rsegs Q0 (MS (RB f fr (Z_to_bv 64 ret) (Z_to_bv 64 spc) t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7
                         s5' s6' s10' s11' t3 t4 t5 t6)
                     F (Z_to_bv 64 BUILD_DT1_SINGLE) fc None mc (seg_rom rsegs)).
  Proof.
    intros fr f spc j n w56 mc J ret nn SS v D a0 a1 a2 a3 t0 t1 t2 a4 a5 a6 a7 s5' s6' s10' s11' t3 t4 t5 t6
      HK Hp0 Ho0 PI Hret Hn9 Hn1 LD E0 E1 E2 E3 HSb HAS HS7 HSN DSO DSR RSSon K.
    hide_secO. keep_F0. bounds0.
    apply (ExecF.evtF_evt rsegs ExecF.RNG_all).
    eapply cl_bd_F0 with (Q := fun _ _ _ _ _ _ => Q0) (fr := fr) (f := f) (spc := spc) (j := j) (n := n) (w56 := w56) (mc := mc) (J := J)
      (ret := ret) (nn := nn) (SS := SS) (v := v) (D := D);
      try eassumption; try assumption; try (apply bmb_KR_Q00; all_rng); all_rng.
  Qed.

End OfF.
