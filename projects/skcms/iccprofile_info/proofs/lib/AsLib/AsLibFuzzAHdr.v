(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.skcms.iccprofile_info.images Require Import Asan.
From OSSVerify.Proofs.skcms.iccprofile_info.lib.Info Require Import PropExec CatExec CatSim SeqExec StoreOk SymExec Hoare Frame PropExecFP.
From OSSVerify.Proofs.skcms.iccprofile_info.lib.Info Require Import LibDefs LibFrame LibTagsSpec FuzzContract.
From OSSVerify.Proofs.skcms.iccprofile_info.lib.AsLib Require Import AsSymExec AsSymExecSound AsSymRun AsSymDrive AsSymCall AsFuzzContract AsLibShadow AsLibDefs AsRtSpec AsLibTagsSpec AsLibWP1Spec AsLibTagsLib AsLibFPLib AsLibParseLib AsLibFrame AsLibEnv AsLibParseSpec AsLibKit AsLibPlace.
From OSSVerify.Proofs.skcms.iccprofile_info.lib.AsLib Require Import AsSymDriveLZ.
Import ListNotations.
Open Scope bv_scope.
Import ASX. Import ASXS.
Ltac Zify.zify_post_hook ::= idtac.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Unset Lia Cache. Unset Nia Cache.   (* [comment removed for export] *)

#[local] Abbreviation SEGS := Asan.M.loaded_segments.

(* [comment removed for export] *)
Ltac lia1f := first [ clia | match goal with H : _ \/ _ |- _ => (destruct H as [H|H]; clia) end ].

(* [comment removed for export] *)
Ltac flia := first [ clia | lia ].
#[local] Abbreviation TP := 0x5d9b70%Z.
#[local] Abbreviation GF := 0x5d9240%Z.
#[local] Abbreviation DEPTH := 3584%Z.

(* [comment removed for export] *)
Ltac in_lit := cbn; repeat (first [left; reflexivity | right]).

(* [comment removed for export] *)
Lemma realign160 : forall sp : word, (bv_unsigned sp mod 16 = 0)%Z -> (176 <= bv_unsigned sp)%Z ->
  let u := bv_unsigned (alu64 ALU_AND (alu64 ALU_ADD sp (Z_to_bv 64 (-160))) (Z_to_bv 64 (-32))) in
  (u mod 32 = 0)%Z /\ (bv_unsigned sp - 176 <= u <= bv_unsigned sp - 160)%Z.
Proof.
  intros sp Hal Hge. cbv zeta. pose proof (u64_range sp).
  rewrite u_and64, u_add64, !u_lit64. unfold two64.
  change ((-32) mod 2 ^ 64)%Z with (2 ^ 64 - 2 ^ 5)%Z.
  Ltac Zify.zify_post_hook ::= Z.div_mod_to_equations.
  rewrite land_highmask by flia. flia.
  Ltac Zify.zify_post_hook ::= idtac.
Qed.

(* [comment removed for export] *)
Lemma gfool_apart :
  (forall a v, In (a, v) (aa_c64 asan_abi) -> (a + 8 <= GF \/ GF + 4 <= a)%Z) /\
  (forall a v, In (a, v) (aa_c32 asan_abi) -> (a + 4 <= GF \/ GF + 4 <= a)%Z) /\
  (forall a v, In (a, v) (aa_c8 asan_abi) -> (a + 1 <= GF \/ GF + 4 <= a)%Z) /\
  (forall a, In a (aa_r64 asan_abi) -> (a + 8 <= GF \/ GF + 4 <= a)%Z) /\
  (forall a v, In (a, v) (aa_shb asan_abi) -> (a + 1 <= GF \/ GF + 4 <= a)%Z) /\
  (forall lo hi, In (lo, hi) (aa_ro asan_abi) -> (hi <= GF \/ GF + 4 <= lo)%Z).
Proof.
  cbn -[Z.le Z.add].
  repeat split; intros;
  repeat match goal with H : _ \/ _ |- _ => destruct H as [H|H] | H : False |- _ => destruct H end;
  try match goal with H : (_, _) = (_, _) |- _ => injection H as <- <- end; try subst; cbn; flia.
Qed.

From OSSVerify.Proofs.skcms.iccprofile_info.lib.AsLib Require Import AsLibFuzzADefs.
From Stdlib Require Import Zify.
(* [comment removed for export] *)
Local Ltac el_t1 := (intros; Zify.zify_pre_hook; zify_elim_let; zify_op; zify_iter_specs; Zify.zify_post_hook); xlia zchecker.
(* [comment removed for export] *)
Local Ltac el_dm_pose x k := let v := eval vm_compute in k in lazymatch v with Zpos _ =>   (* [comment removed for export] *)
  lazymatch goal with _ : (x = k * (x / k) + x mod k)%Z |- _ => fail | _ =>
    pose proof (Z.div_mod x k ltac:(vm_compute; discriminate)); pose proof (Z.mod_pos_bound x k ltac:(vm_compute; reflexivity)) end end.
Local Ltac el_dm := repeat match goal with
  | |- context [ (?x / ?k)%Z ] => el_dm_pose x k
  | |- context [ (?x mod ?k)%Z ] => el_dm_pose x k
  | H : ?T |- _ => lazymatch T with (_ <= _)%Z => idtac | (_ < _)%Z => idtac | @eq Z _ _ => idtac | _ /\ _ => idtac | _ \/ _ => idtac end;
      match T with context [ (?x / ?k)%Z ] => el_dm_pose x k | context [ (?x mod ?k)%Z ] => el_dm_pose x k end
  end.
Local Ltac el_lia_core3 := first [ el_t1 | Zify.zify; xlia zchecker ].   (* [comment removed for export] *)
Local Ltac el_lia_core := first [ el_t1 | ((progress el_dm); el_t1) ].
Local Ltac el_goal_has_var := match goal with |- ?G => match G with context [?x] => is_var x end end.
Local Ltac Lia.lia ::= tryif el_goal_has_var then el_lia_core else first [ solve [clear; el_lia_core] | el_lia_core ].
(* [comment removed for export] *)
(* [comment removed for export] *)
Local Ltac ev_simpl E ::=
  lazymatch goal with |- ?G =>
    let G1 := match tt with | _ => eval unfold E in G | _ => G end in
    let G2 := eval lazy [ev eb vals_ev blobs_ev nth app junk_vals fjunk_vals] in G1 in
    change G2
  end.
Local Ltac ev_simpl_in E H ::= try unfold E in H; lazy [ev eb vals_ev blobs_ev nth app junk_vals fjunk_vals] in H.
(* [comment removed for export] *)
#[local] Ltac AsSymDrive.run_fp_with_h HR HF HK fuel stops scr chints keep extra ::= run_fp_with_h_lz HR HF HK fuel stops scr chints keep extra.
#[local] Ltac AsSymDrive.branch_case_with HR HF HK Hc ::= branch_case_with_lz HR HF HK Hc.
Section Proof.
  Variable ceil : Z.
  (* [comment removed for export] *)
  Hypothesis Hparse : parse_contract_as SEGS as_asan ceil.
  Hypothesis Hgetidx : getidx_contract_as SEGS as_asan ceil.
  Hypothesis Hrte : rte_contract_as SEGS as_asan ceil.
  Hypothesis Hsm5 : stkmalloc5_contract SEGS as_asan ceil.
  Hypothesis Hsf5 : stkfree5_contract SEGS as_asan ceil.
  Hypothesis Hs00 : setsh00_contract SEGS as_asan.
  Hypothesis Hsf8 : setshf8_contract SEGS as_asan.

  Hypothesis Hparse0 : parse0_contract ceil.

  (* [comment removed for export] *)
  Variables (FP0 : FPState) (regs : bvmap 5 word) (mem rom : word -> option byte).
  Variables (ret sp data : word) (n : Z) (bs : list byte) (fs : Z) (h0 h5 ctx thr t48 t56 dtls v24 : word).

  (* [comment removed for export] *)
  Hypothesis HALL : FENV ceil regs mem ret sp data n bs fs h0 h5 ctx thr t48 t56 dtls v24.

  (* [comment removed for export] *)
  Ltac need_nums := pose proof (Hn HALL) as Hn; pose proof (Hal HALL) as Hal; pose proof (Hdal HALL) as Hdal;
                    pose proof (Hclo HALL) as Hclo; pose proof (Hsplo HALL) as Hsplo; pose proof (Hsphi HALL) as Hsphi;
                    pose proof (Hfslo HALL) as Hfslo; pose proof (Hfshi HALL) as Hfshi; pose proof (Hfsal HALL) as Hfsal;
                    unfold FS_SIZE in Hsplo, Hfslo, Hfshi; app_facts.
  Ltac need_cells := pose proof (Hc64 HALL) as Hc64; pose proof (Hc32 HALL) as Hc32; pose proof (Hc8 HALL) as Hc8;
                     pose proof (Hr64 HALL) as Hr64; pose proof (Hshb HALL) as Hshb; pose proof (Hro HALL) as Hro.
  Ltac need_chain := pose proof (Htsd HALL) as Htsd; pose proof (Hctxok HALL) as Hctxok; pose proof (Hctx HALL) as Hctx;
                     pose proof (Ht48ok HALL) as Ht48ok; pose proof (Ht56ok HALL) as Ht56ok; pose proof (Ht48 HALL) as Ht48;
                     pose proof (Ht56 HALL) as Ht56; pose proof (Hdtls HALL) as Hdtls; pose proof (Hdtlsnz HALL) as Hdtlsnz;
                     pose proof (Hv24ok HALL) as Hv24ok; pose proof (Hv24 HALL) as Hv24; pose proof (Hv24nz HALL) as Hv24nz.
  Ltac need_fs := pose proof (Hfscell HALL) as Hfscell; pose proof (Hh0 HALL) as Hh0; pose proof (Hh5 HALL) as Hh5;
                  pose proof (Hssl HALL) as Hssl; pose proof (Hngc HALL) as Hngc; pose proof (Hfl0 HALL) as Hfl0; pose proof (Hfl5 HALL) as Hfl5.
  Ltac need_wr := pose proof (Hstw HALL) as Hstw; pose proof (Hgfw HALL) as Hgfw; pose proof (Hgfr HALL) as Hgfr;
                  pose proof (Hwh0 HALL) as Hwh0; pose proof (Hwh5 HALL) as Hwh5; pose proof (Hwfl0 HALL) as Hwfl0;
                  pose proof (Hwfl5 HALL) as Hwfl5; pose proof (Hwfr0 HALL) as Hwfr0; pose proof (Hwfr5 HALL) as Hwfr5;
                  pose proof (Hwsf0 HALL) as Hwsf0; pose proof (Hwsf5 HALL) as Hwsf5.
  Ltac need_data := pose proof (Hdpl HALL) as Hdpl; pose proof (Hblob HALL) as Hblob; pose proof (Hshd HALL) as Hshd;
                    pose proof (Hbs HALL) as Hbs; pose proof (Hstsh HALL) as Hstsh; unfold FS_SIZE in Hdpl.
  Ltac need_regs := pose proof (Hra HALL) as Hra; pose proof (Hret HALL) as Hret; pose proof (Hsp HALL) as Hsp;
                    pose proof (Htp HALL) as Htp; pose proof (Ha0 HALL) as Ha0; pose proof (Ha1 HALL) as Ha1.

  (* [comment removed for export] *)
  Definition pos : Z := (bv_unsigned h5 mod 512)%Z.
  Definition F : Z := (fs + 0x509000 + 2048 * pos)%Z.          (* [comment removed for export] *)
  Definition fa : Z := (fs + 0x8c00 + pos)%Z.                   (* [comment removed for export] *)
  #[local] Notation P := (F + 64)%Z.
  #[local] Notation T := (F + 1168)%Z.
  #[local] Notation SF := (SB + F / 8)%Z.
  Definition Uw : word := alu64 ALU_AND (alu64 ALU_ADD sp (Z_to_bv 64 (-160))) (Z_to_bv 64 (-32)).
  #[local] Abbreviation s := (bv_unsigned sp).

  Lemma F_eq : F = sm_frame 5 2048 fs pos. Proof. unfold F, sm_frame, FS_FRAMES0. flia. Qed.
  Lemma fa_eq : fa = sm_flag 0x7c00 fs pos. Proof. unfold fa, sm_flag, FS_FLAGS0. flia. Qed.
  Lemma pos_eq : pos = sm_pos 512 h5. Proof. reflexivity. Qed.

  (* [comment removed for export] *)
  Lemma placement :
    (0 <= pos < 512)%Z /\
    F = (fs + 0x509000 + 2048 * pos)%Z /\ fa = (fs + 0x8c00 + pos)%Z /\
    (F mod 2048 = 0)%Z /\ (F = 8 * (F / 8))%Z /\ (F / 8 = (fs + 0x509000) / 8 + 256 * pos)%Z /\
    ((fs + 0x509000) = 8 * ((fs + 0x509000) / 8))%Z /\ ((fs + 0x9000) = 8 * ((fs + 0x9000) / 8))%Z /\
    SF = (SB + F / 8)%Z /\ (SF mod 8 = 0)%Z /\
    ((bv_unsigned Uw) mod 32 = 0)%Z /\ (s - 176 <= (bv_unsigned Uw) <= s - 160)%Z /\ ((bv_unsigned Uw) = 8 * ((bv_unsigned Uw) / 8))%Z /\ (s = 8 * (s / 8))%Z /\
    ((s - DEPTH) = 8 * ((s - DEPTH) / 8))%Z /\
    (appm (fs) 0xb09000 /\ (0 < fs)%Z) /\ (fs + 0xb09000 <= ceil)%Z /\ ((AS_STKLO <= ceil)%Z /\ (ceil + DEPTH <= s)%Z) /\ (s < 2 ^ 47)%Z.
  Proof.
    need_nums.
    assert (Hp : (0 <= pos < 512)%Z) by (unfold pos; apply Z.mod_pos_bound; flia).
    pose proof (realign160 sp Hal ltac:(flia)) as [U1 U2]. fold Uw in U1, U2.
    Ltac Zify.zify_post_hook ::= Z.div_mod_to_equations.
    assert (A1 : (F mod 2048 = 0)%Z) by (unfold F; clear -Hfsal Hp; flia).
    assert (A2 : (F / 8 = (fs + 0x509000) / 8 + 256 * pos)%Z) by (unfold F; clear -Hfsal Hp; flia).
    assert (A3 : ((fs + 0x509000) = 8 * ((fs + 0x509000) / 8))%Z) by (clear -Hfsal; flia).
    assert (A3' : ((fs + 0x9000) = 8 * ((fs + 0x9000) / 8))%Z) by (clear -Hfsal; flia).
    assert (A4 : (F = 8 * (F / 8))%Z) by (clear -A1; flia).
    assert (A5 : (SF mod 8 = 0)%Z) by (unfold SB; rewrite A2; clear -Hfsal Hp; flia).
    assert (A6 : ((bv_unsigned Uw) = 8 * ((bv_unsigned Uw) / 8))%Z) by (clear -U1; flia).
    assert (A7 : (s = 8 * (s / 8))%Z) by (clear -Hal; flia).
    assert (A8 : ((s - DEPTH) = 8 * ((s - DEPTH) / 8))%Z) by (clear -Hal; flia).
    Ltac Zify.zify_post_hook ::= idtac.
    repeat match goal with |- _ /\ _ => split end; first [assumption | reflexivity | flia].
  Qed.

  Lemma F8k : forall k, (k mod 8 = 0)%Z -> ((F + k) mod 8 = 0)%Z.
  Proof. intros k Hk. pose proof placement as (_ & _ & _ & P3 & _). apply mod_add_multiple; [flia | apply (mod_down F 8 256); [flia|flia|exact P3] | exact Hk]. Qed.

  (* [comment removed for export] *)
  Lemma nums_zone : (fs + 0xb09000 <= 0x7fff7000 \/ 0x10007fff8000 <= fs)%Z /\ (fs + 0xb09000 <= 0x10000 \/ 0x5fc000 <= fs)%Z.
  Proof. need_nums. exact (conj (app_sh_lit _ _ Hfslo) (app_img_lit _ _ Hfslo)). Qed.
  Ltac nlia := first [ (pose proof placement as NUMP; clear - NUMP; lia)
                     | (pose proof placement as NUMP; pose proof nums_zone as NUMZ; clear - NUMP NUMZ; dlia) ].
  Ltac flia ::= first [ nlia | clia | lia ].
  Ltac solve_apart ::=
    unfold apart; repeat (apply Forall_cons; [cbn [fst snd]; rewrite ?u_small_frame by flia; first [nlia | lia1f | (app_sh; lia1f) | (app_img; lia1f) | idtac] |]);
    try apply Forall_nil.
  Ltac place_app ::=
    first [ assumption
          | match goal with H : appm ?a ?m /\ _ |- appm ?a ?m => exact (proj1 H) end
          | match goal with H : (appm ?a ?m /\ _) /\ _ |- appm ?a ?m => exact (proj1 (proj1 H)) end
          | match goal with H : appm ?a ?m |- appm ?b ?k => apply (app_shrink a m b k H); flia end
          | match goal with H : appm ?a ?m /\ _ |- appm ?b ?k => apply (app_shrink a m b k (proj1 H)); flia end
          | match goal with H : (appm ?a ?m /\ _) /\ _ |- appm ?b ?k => apply (app_shrink a m b k (proj1 (proj1 H))); flia end ].
  Ltac plc ::= first [ nlia | clia | place_app | (split; plc) | (app_facts; clia) | lia ].


  #[local] Opaque Uw.

  (* [comment removed for export] *)
  Definition BIGF : list (word * Z) := as_mod asan_abi s fs.

  Definition in_bigf (b : word) (m : Z) : Prop :=
    exists b' n', In (b', n') BIGF /\ (bv_unsigned b' <= bv_unsigned b)%Z /\ (bv_unsigned b + m <= bv_unsigned b' + n')%Z.
  Lemma bincl_of : forall rs, Forall (fun r => in_bigf (fst r) (snd r)) rs -> regions_incl rs BIGF.
  Proof. intros rs H b m Hin. rewrite Forall_forall in H. exact (H (b, m) Hin). Qed.
  Lemma frame_BIGF_app : forall M1 M2 l,
    frame_mod mem M1 BIGF -> frame_mod M1 M2 l -> regions_incl l BIGF -> frame_mod mem M2 BIGF.
  Proof. intros M1 M2 l HA HB Hl. eapply frame_mod_incl; [| exact (frame_mod_trans _ _ _ _ _ HA HB)].
         intros b m Hin. apply in_app_or in Hin as [Hin|Hin]; [exists b, m; split; [exact Hin| flia] | exact (Hl b m Hin)]. Qed.

  Lemma in_stack : forall a m, (s - DEPTH <= a)%Z -> (0 <= m)%Z -> (a + m <= s)%Z -> in_bigf (Z_to_bv 64 a) m.
  Proof. intros a m H1 H2 H3. need_nums. pose proof (u64_range sp).
         exists (Z_to_bv 64 (s - DEPTH)), DEPTH. split; [first [solve [cbn; repeat (first [left; reflexivity | right])] | (cbn; tauto)]|]. rewrite !u_small by flia. flia. Qed.
  Lemma in_gfool : in_bigf (Z_to_bv 64 GF) 4.
  Proof. exists (Z_to_bv 64 GF), 4%Z. split; [first [solve [cbn; repeat (first [left; reflexivity | right])] | (cbn; tauto)]|]. flia. Qed.
  Lemma in_hint0 : in_bigf (Z_to_bv 64 (fs + 0)) 8.
  Proof. exists (Z_to_bv 64 (fs + FS_HINT0)), 8%Z. split; [first [solve [cbn; repeat (first [left; reflexivity | right])] | (cbn; tauto)]|]. unfold FS_HINT0. flia. Qed.
  Lemma in_hint5 : in_bigf (Z_to_bv 64 (fs + 40)) 8.
  Proof. exists (Z_to_bv 64 (fs + FS_HINT5)), 8%Z. split; [first [solve [cbn; repeat (first [left; reflexivity | right])] | (cbn; tauto)]|]. unfold FS_HINT5. flia. Qed.
  Lemma in_flags0 : forall a m, (fs + 0x1000 <= a)%Z -> (0 <= m)%Z -> (a + m <= fs + 0x5000)%Z -> in_bigf (Z_to_bv 64 a) m.
  Proof. intros a m H1 H2 H3. need_nums.
         exists (Z_to_bv 64 (fs + FS_FLAGS0)), FS_FLAGS0_LEN. split; [first [solve [cbn; repeat (first [left; reflexivity | right])] | (cbn; tauto)]|]. unfold FS_FLAGS0, FS_FLAGS0_LEN. rewrite !u_small by flia. flia. Qed.
  Lemma in_flags5 : forall a m, (fs + 0x8c00 <= a)%Z -> (0 <= m)%Z -> (a + m <= fs + 0x8e00)%Z -> in_bigf (Z_to_bv 64 a) m.
  Proof. intros a m H1 H2 H3. need_nums.
         exists (Z_to_bv 64 (fs + FS_FLAGS5)), FS_FLAGS5_LEN. split; [first [solve [cbn; repeat (first [left; reflexivity | right])] | (cbn; tauto)]|]. unfold FS_FLAGS5, FS_FLAGS5_LEN. rewrite !u_small by flia. flia. Qed.
  Lemma in_frames0 : forall a m, (fs + 0x9000 <= a)%Z -> (0 <= m)%Z -> (a + m <= fs + 0x109000)%Z -> in_bigf (Z_to_bv 64 a) m.
  Proof. intros a m H1 H2 H3. need_nums.
         exists (Z_to_bv 64 (fs + FS_FRAMES0)), FS_FRAMES_LEN. split; [first [solve [cbn; repeat (first [left; reflexivity | right])] | (cbn; tauto)]|]. unfold FS_FRAMES0, FS_FRAMES_LEN. rewrite !u_small by flia. flia. Qed.
  Lemma in_frames5 : forall a m, (fs + 0x509000 <= a)%Z -> (0 <= m)%Z -> (a + m <= fs + 0x609000)%Z -> in_bigf (Z_to_bv 64 a) m.
  Proof. intros a m H1 H2 H3. need_nums.
         exists (Z_to_bv 64 (fs + FS_FRAMES5)), FS_FRAMES_LEN. split; [first [solve [cbn; repeat (first [left; reflexivity | right])] | (cbn; tauto)]|]. unfold FS_FRAMES5, FS_FRAMES_LEN. rewrite !u_small by flia. flia. Qed.
  Ltac Zify.zify_post_hook ::= Z.div_mod_to_equations.
  Lemma in_shframes0 : forall a m, (SB + (fs + 0x9000) / 8 <= a)%Z -> (0 <= m)%Z -> (a + m <= SB + (fs + 0x9000) / 8 + 0x20000)%Z -> in_bigf (Z_to_bv 64 a) m.
  Proof. intros a m H1 H2 H3. need_nums.
         exists (Z_to_bv 64 (AS_SB + (fs + FS_FRAMES0) / 8)), FS_SHFRAMES_LEN. split; [first [solve [cbn; repeat (first [left; reflexivity | right])] | (cbn; tauto)]|]. unfold AS_SB, SB, FS_FRAMES0, FS_SHFRAMES_LEN in *. rewrite !u_small by flia. flia. Qed.
  Lemma in_shframes5 : forall a m, (SB + (fs + 0x509000) / 8 <= a)%Z -> (0 <= m)%Z -> (a + m <= SB + (fs + 0x509000) / 8 + 0x20000)%Z -> in_bigf (Z_to_bv 64 a) m.
  Proof. intros a m H1 H2 H3. need_nums.
         exists (Z_to_bv 64 (AS_SB + (fs + FS_FRAMES5) / 8)), FS_SHFRAMES_LEN. split; [first [solve [cbn; repeat (first [left; reflexivity | right])] | (cbn; tauto)]|]. unfold AS_SB, SB, FS_FRAMES5, FS_SHFRAMES_LEN in *. rewrite !u_small by flia. flia. Qed.
  Ltac Zify.zify_post_hook ::= idtac.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Ltac Zify.zify_post_hook ::= Z.div_mod_to_equations.
  (* [comment removed for export] *)
  Ltac lia1 := first [ clia | match goal with H : _ \/ _ |- _ => (destruct H as [H|H]; clia) end ].
  Ltac lia2 := first [ lia1 | match goal with H : _ \/ _ |- _ => (destruct H as [H|H]; lia1) end ].
  Ltac zlia := unfold in_env_zone, AS_IMGLO, AS_IMGHI, AS_SIMGLO, AS_SIMGHI in *; cbn -[Z.div]; flia.
  Lemma apart_env_bigf : forall a w, in_env_zone a w -> (0 <= w)%Z -> (a + w <= GF \/ GF + 4 <= a)%Z -> apart a w BIGF.
  Proof.
    intros a w H1 H2 H3. need_nums. pose proof (u64_range sp).
    pose proof (app_sh_lit _ _ Hfslo) as Fsh. pose proof (app_img_lit _ _ Hfslo) as Fim.
    unfold in_env_zone, AS_IMGLO, AS_IMGHI, AS_SIMGLO, AS_SIMGHI in H1.
    unfold apart, BIGF, as_mod. cbn [aa_depth aa_gfool asan_abi].
    unfold FS_HINT0, FS_HINT5, FS_FLAGS0, FS_FLAGS0_LEN, FS_FLAGS5, FS_FLAGS5_LEN, FS_FRAMES0, FS_FRAMES5, FS_FRAMES_LEN, FS_SHFRAMES_LEN, AS_SB.
    destruct H1 as [H1|H1]; (repeat (apply Forall_cons); [..|apply Forall_nil]; cbn [fst snd]; rewrite u_small by clia; lia1).
  Qed.
  Lemma apart_heap_bigf : forall a, heap_cell_ok ceil a fs -> apart a 8 BIGF.
  Proof.
    intros a (H1 & H2 & H3). need_nums. pose proof (u64_range sp). app_facts.
    pose proof (app_sh_lit _ _ H1) as Ash. pose proof (app_img_lit _ _ H1) as Aim. pose proof (app_sh_lit _ _ Hfslo) as Fsh.
    unfold FS_SIZE in *.
    unfold apart, BIGF, as_mod. cbn [aa_depth aa_gfool asan_abi].
    unfold FS_HINT0, FS_HINT5, FS_FLAGS0, FS_FLAGS0_LEN, FS_FLAGS5, FS_FLAGS5_LEN, FS_FRAMES0, FS_FRAMES5, FS_FRAMES_LEN, FS_SHFRAMES_LEN, AS_SB.
    repeat (apply Forall_cons); [..|apply Forall_nil]; cbn [fst snd]; rewrite u_small by clia; lia1.
  Qed.
  (* [comment removed for export] *)
  Lemma apart_data_bigf : (0 < n)%Z -> apart (bv_unsigned data) n BIGF /\ apart (SB + bv_unsigned data / 8) (n / 8 + 1) BIGF.
  Proof.
    intros Hn0. need_nums. need_data. destruct (Hdpl Hn0) as (D1 & D2 & D3). pose proof (u64_range sp). app_facts.
    pose proof (app_sh_lit _ _ D1) as Dsh. pose proof (app_img_lit _ _ D1) as Dim. pose proof (app_sh_lit _ _ Hfslo) as Fsh.
    unfold apart, BIGF, as_mod. cbn [aa_depth aa_gfool asan_abi].
    unfold FS_HINT0, FS_HINT5, FS_FLAGS0, FS_FLAGS0_LEN, FS_FLAGS5, FS_FLAGS5_LEN, FS_FRAMES0, FS_FRAMES5, FS_FRAMES_LEN, FS_SHFRAMES_LEN, AS_SB, SB.
    split; (repeat (apply Forall_cons); [..|apply Forall_nil]; cbn [fst snd]; rewrite u_small by clia; lia1).
  Qed.
  Lemma apart_stsh_bigf : apart (SB + (s - DEPTH) / 8) (DEPTH / 8) BIGF.
  Proof.
    need_nums. pose proof (u64_range sp). pose proof (app_sh_lit _ _ Hfslo) as Fsh.
    unfold apart, BIGF, as_mod. cbn [aa_depth aa_gfool asan_abi].
    unfold FS_HINT0, FS_HINT5, FS_FLAGS0, FS_FLAGS0_LEN, FS_FLAGS5, FS_FLAGS5_LEN, FS_FRAMES0, FS_FRAMES5, FS_FRAMES_LEN, FS_SHFRAMES_LEN, AS_SB, SB.
    repeat (apply Forall_cons); [..|apply Forall_nil]; cbn [fst snd]; rewrite u_small by clia; lia1.
  Qed.
  Lemma apart_hdr_bigf : apart (fs + FS_SSL) 9 BIGF.
  Proof.
    need_nums. pose proof (u64_range sp). pose proof (app_sh_lit _ _ Hfslo) as Fsh. pose proof (app_img_lit _ _ Hfslo) as Fim.
    unfold apart, BIGF, as_mod. cbn [aa_depth aa_gfool asan_abi].
    unfold FS_SSL, FS_HINT0, FS_HINT5, FS_FLAGS0, FS_FLAGS0_LEN, FS_FLAGS5, FS_FLAGS5_LEN, FS_FRAMES0, FS_FRAMES5, FS_FRAMES_LEN, FS_SHFRAMES_LEN, AS_SB, SB.
    repeat (apply Forall_cons); [..|apply Forall_nil]; cbn [fst snd]; rewrite u_small by clia; lia1.
  Qed.
  Ltac Zify.zify_post_hook ::= idtac.

  (* [comment removed for export] *)
  Lemma as_env_bigf : forall M, frame_mod mem M BIGF -> as_env SEGS ceil asan_abi fs (CH ctx thr t48 t56 dtls v24) M.
  Proof.
    intros M Hf. need_cells. need_chain. pose proof asan_abi_low as (L64 & L32 & L8 & LR & LS & LRO & T1 & T2).
    pose proof gfool_apart as (G64 & G32 & G8 & GR & GS & GRO). unfold in_env_zone, AS_IMGLO, AS_IMGHI, AS_SIMGLO, AS_SIMGHI in T1, T2.
    split; [|split; [|split]].
    - split; [|split; [|split]].
      + intros a v Hin. pose proof (L64 a v Hin). pose proof (G64 a v Hin).
        eapply acell_frame; [exact Hf | apply Hc64; exact Hin | zlia | cbn; zlia | apply apart_env_bigf; first [assumption | flia]].
      + intros a v Hin. pose proof (L32 a v Hin). pose proof (G32 a v Hin).
        eapply acell_frame; [exact Hf | apply Hc32; exact Hin | zlia | cbn; zlia | apply apart_env_bigf; first [assumption | flia]].
      + intros a v Hin. pose proof (L8 a v Hin). pose proof (G8 a v Hin).
        eapply acell_frame; [exact Hf | apply Hc8; exact Hin | zlia | cbn; zlia | apply apart_env_bigf; first [assumption | flia]].
      + intros a Hin. pose proof (LR a Hin). pose proof (GR a Hin).
        eapply areadable_frame; [exact Hf | apply Hr64; exact Hin | zlia | cbn; zlia | apply apart_env_bigf; first [assumption | flia]].
    - intros a v Hin. pose proof (LS a v Hin). pose proof (GS a v Hin).
      rewrite (byte_frame mem M BIGF a Hf ltac:(zlia)); [apply Hshb; exact Hin|]. apply apart_env_bigf; first [assumption | (unfold in_env_zone, AS_IMGLO, AS_IMGHI, AS_SIMGLO, AS_SIMGHI in *; cbn; flia) | (cbn; flia)].
    - intros lo hi i Hin Hi. pose proof (LRO lo hi Hin). pose proof (GRO lo hi Hin).
      rewrite (byte_frame mem M BIGF i Hf ltac:(zlia)); [apply (Hro lo hi i Hin Hi)|]. apply apart_env_bigf; first [assumption | (unfold in_env_zone, AS_IMGLO, AS_IMGHI, AS_SIMGLO, AS_SIMGHI in *; cbn; flia) | (cbn; flia)].
    - unfold env_chain. cbn [ch_ctx ch_thr ch_t48 ch_t56 ch_dtls ch_v24 aa_tsdv aa_tp asan_abi].
      pose proof Hctxok as (?&?&?). pose proof Ht48ok as (?&?&?). pose proof Ht56ok as (?&?&?). pose proof Hv24ok as (?&?&?). app_facts.
      
      split; [eapply acellw_frame; [exact Hf | exact Htsd | flia | flia | apply apart_env_bigf; first [assumption | (unfold in_env_zone, AS_IMGLO, AS_IMGHI, AS_SIMGLO, AS_SIMGHI in *; cbn; flia) | (cbn; flia)]]|].
      split; [exact Hctxok|].
      split; [eapply acellw_frame; [exact Hf | exact Hctx | flia | flia | apply apart_heap_bigf; exact Hctxok]|].
      split; [exact Ht48ok|]. split; [exact Ht56ok|].
      split; [eapply acellw_frame; [exact Hf | exact Ht48 | flia | flia | apply apart_heap_bigf; exact Ht48ok]|].
      split; [eapply acellw_frame; [exact Hf | exact Ht56 | flia | flia | apply apart_heap_bigf; exact Ht56ok]|].
      split; [eapply acellw_frame; [exact Hf | exact Hdtls | flia | flia | apply apart_env_bigf; first [assumption | (unfold in_env_zone, AS_IMGLO, AS_IMGHI, AS_SIMGLO, AS_SIMGHI in *; cbn; flia) | (cbn; flia)]]|].
      split; [exact Hdtlsnz|]. split; [exact Hv24ok|].
      split; [eapply acellw_frame; [exact Hf | exact Hv24 | flia | flia | apply apart_heap_bigf; exact Hv24ok]|].
      exact Hv24nz.
  Qed.

  Lemma fs_hdr_bigf : forall M, frame_mod mem M BIGF -> fs_hdr SEGS ceil asan_abi fs M.
  Proof.
    intros M Hf. need_nums. need_fs. unfold fs_hdr. cbn [aa_tp asan_abi].
    pose proof apart_hdr_bigf as HA. unfold FS_SSL, FS_NEEDSGC in *.
    split; [eapply acell_frame; [exact Hf | exact Hfscell | flia | cbn; flia | apply apart_env_bigf; first [assumption | (unfold in_env_zone, AS_IMGLO, AS_IMGHI, AS_SIMGLO, AS_SIMGHI in *; cbn; flia) | (cbn; flia)]]|].
    split; [eapply acell_frame; [exact Hf | exact Hssl | flia | cbn; flia | eapply apart_sub; [exact HA | flia | cbn; flia | cbn; flia]]|].
    split; [eapply acell_frame; [exact Hf | exact Hngc | flia | cbn; flia | eapply apart_sub; [exact HA | flia | cbn; flia | cbn; flia]]|].
    unfold FS_SIZE. split; [exact Hfslo | flia].
  Qed.

  Lemma fs_writable_bigf : forall M, frame_mod mem M BIGF -> fs_writable SEGS fs M.
  Proof.
    intros M Hf. need_wr. unfold fs_writable.
    repeat match goal with |- _ /\ _ => split end; (eapply awritable_frame; [exact Hf | assumption]).
  Qed.

  Lemma data_bigf : forall M, frame_mod mem M BIGF -> (0 < n)%Z ->
    as_data_ok ceil M data n bs /\ (bv_unsigned data + n <= fs \/ fs + FS_SIZE <= bv_unsigned data)%Z.
  Proof.
    intros M Hf Hn0. need_nums. need_data. destruct (Hdpl Hn0) as (D1 & D2 & D3). destruct (apart_data_bigf Hn0) as [A1 A2]. app_facts.
    pose proof (u64_range data).
    split; [|exact D3]. split; [|split; [unfold heapish; plc | split; [exact Hdal|]]].
    - eapply data_ok_frame; [exact Hf | | exact A1]. split; [flia|]. split; [exact Hbs|]. split; [flia|]. split; [flia|]. exact Hblob.
    - split; [apply (mod_down _ 8 2); [flia|flia|exact Hdal]|]. intros g Hg1 Hg2.
      rewrite (byte_frame mem M BIGF (SB + g) Hf ltac:(unfold SB; flia)).
      + unfold ashdata, AS_SB in Hshd. unfold SB, shad_byte, as_shad_byte in *. apply Hshd; assumption.
      + eapply apart_sub; [exact A2 | unfold SB; flia | | ].
        Ltac Zify.zify_post_hook ::= Z.div_mod_to_equations. all: unfold SB; flia. Ltac Zify.zify_post_hook ::= idtac.
  Qed.

  Lemma stsh_bigf : forall M, frame_mod mem M BIGF -> shz M (s - DEPTH) (DEPTH / 8).
  Proof.
    intros M Hf. need_nums. need_data. pose proof placement as PL. hide PL. pose proof (u64_range sp).
    split.
    - pose proof (unhide PL) as (_&_&_&_&_&_&_&_&_&_&_&_&_&_&A8&_). clear PL. Ltac Zify.zify_post_hook ::= Z.div_mod_to_equations. flia. Ltac Zify.zify_post_hook ::= idtac.
    - intros j Hj. rewrite (byte_frame mem M BIGF (SB + (s - DEPTH) / 8 + j) Hf).
      + unfold azero, AS_SB in Hstsh. unfold SB. apply Hstsh. exact Hj.
      + clear PL. unfold SB. Ltac Zify.zify_post_hook ::= Z.div_mod_to_equations. flia. Ltac Zify.zify_post_hook ::= idtac.
      + eapply apart_sub; [exact apart_stsh_bigf | | flia | flia]. clear PL. unfold SB. Ltac Zify.zify_post_hook ::= Z.div_mod_to_equations. flia. Ltac Zify.zify_post_hook ::= idtac.
  Qed.

  (* [comment removed for export] *)
  Lemma writable_at : forall M lo k lo' k', frame_mod mem M BIGF -> awritable SEGS mem lo k ->
    (0 <= lo)%Z -> (lo <= lo')%Z -> (0 < k')%Z -> (lo' + k' <= lo + k)%Z -> (lo + k <= 2 ^ 64)%Z -> writable SEGS M lo' k'.
  Proof.
    intros M lo k lo' k' Hf Hw H1 H2 H3 H4 H5. eapply writable_sub; [| exact H2 | flia | exact H4].
    split; [flia|]. split; [flia|]. split; [flia|]. eapply awritable_frame; [exact Hf | exact Hw].
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Definition SAVED13 (M : word -> option byte) : Prop :=
    cell64 SEGS M (s - 8) (getr regs 1) /\ cell64 SEGS M (s - 16) (getr regs 8) /\ cell64 SEGS M (s - 24) (getr regs 9) /\
    cell64 SEGS M (s - 32) (getr regs 18) /\ cell64 SEGS M (s - 40) (getr regs 19) /\ cell64 SEGS M (s - 48) (getr regs 20) /\
    cell64 SEGS M (s - 56) (getr regs 21) /\ cell64 SEGS M (s - 64) (getr regs 22) /\ cell64 SEGS M (s - 72) (getr regs 23) /\
    cell64 SEGS M (s - 80) (getr regs 24) /\ cell64 SEGS M (s - 88) (getr regs 25) /\ cell64 SEGS M (s - 96) (getr regs 26) /\
    cell64 SEGS M (s - 104) (getr regs 27).

  (* [comment removed for export] *)
  Definition flags5_but (M : word -> option byte) : Prop :=
    forall i, (0 <= i < 0x200)%Z -> i <> pos -> M (Z_to_bv 64 (fs + 0x8c00 + i)) = Some (Z_to_bv 8 0).

  Definition MEMB (M : word -> option byte) : Prop :=
    SAVED13 M /\ frame_mod mem M BIGF /\
    cell64 SEGS M ((bv_unsigned Uw) + 24) (Z_to_bv 64 F) /\ acell SEGS M (F + 2040) 8 fa /\
    fs_flags0_but fs [] M /\ (exists h, acellw SEGS M (fs + FS_HINT0) h) /\ flags5_but M /\
    shz M P 122 /\ (exists gw, LibDefs.cell SEGS M GF 4 gw).

  (* [comment removed for export] *)
  Definition BASE (R : bvmap 5 word) (M : word -> option byte) : Prop :=
    getr R 2 = Uw /\ getr R 9 = Uw /\ getr R 8 = sp /\ getr R 3 = getr regs 3 /\ getr R 4 = getr regs 4 /\
    getr R 19 = Z_to_bv 64 SF /\ getr R 21 = Z_to_bv 64 (SF + 8) /\ getr R 25 = Z_to_bv 64 F /\
    getr R 26 = Z_to_bv 64 SB /\ getr R 27 = Z_to_bv 64 (-8) /\
    MEMB M.

  Lemma SAVED13_frame : forall M M' rs, SAVED13 M -> frame_mod M M' rs -> apart (s - 104) 104 rs -> SAVED13 M'.
  Proof.
    intros M M' rs (C1 & C2 & C3 & C4 & C5 & C6 & C7 & C8 & C9 & C10 & C11 & C12 & C13) Hf Hap. need_nums. pose proof (u64_range sp).
    Ltac sv13 Hf C Hap := eapply cell64_frame; [exact Hf | exact C | flia | flia | eapply apart_sub; [exact Hap | flia | flia | flia]].
    split; [sv13 Hf C1 Hap|]. split; [sv13 Hf C2 Hap|]. split; [sv13 Hf C3 Hap|]. split; [sv13 Hf C4 Hap|].
    split; [sv13 Hf C5 Hap|]. split; [sv13 Hf C6 Hap|]. split; [sv13 Hf C7 Hap|]. split; [sv13 Hf C8 Hap|].
    split; [sv13 Hf C9 Hap|]. split; [sv13 Hf C10 Hap|]. split; [sv13 Hf C11 Hap|]. split; [sv13 Hf C12 Hap|]. sv13 Hf C13 Hap.
  Qed.

  (* [comment removed for export] *)
  Lemma MEMB_frame : forall M M' rs, MEMB M -> frame_mod M M' rs -> regions_incl rs BIGF ->
    apart (s - 104) 104 rs -> apart ((bv_unsigned Uw) + 24) 8 rs -> apart (F + 2040) 8 rs ->
    apart (fs + 0x1000) 0x4000 rs -> apart (fs + 0) 8 rs -> apart (fs + 0x8c00) 0x200 rs ->
    apart (SF + 8) 122 rs -> apart GF 4 rs -> MEMB M'.
  Proof.
    intros M M' rs (M1 & M2 & M3 & M4 & M5 & M6 & M7 & M8 & M9) Hf Hin A1 A2 A3 A4 A5 A6 A7 A8.
    need_nums. pose proof placement as PL. hide PL. pose proof (u64_range sp).
    pose proof (unhide PL) as (P1&P2&P3&_&_&_&_&_&P9&_&_&P12&_).

    split; [eapply SAVED13_frame; [exact M1 | exact Hf | exact A1]|].
    split; [eapply frame_BIGF_app; [exact M2 | exact Hf | exact Hin]|].
    split; [eapply cell64_frame; [exact Hf | exact M3 | flia | flia | exact A2]|].
    split; [eapply acell_frame; [exact Hf | exact M4 | flia | cbn; flia | exact A3]|].
    split. { intros i Hi Hni. unfold FS_FLAGS0, FS_FLAGS0_LEN in *. rewrite (byte_frame M M' rs (fs + 4096 + i) Hf ltac:(flia)); [apply M5; assumption|].
             eapply apart_sub; [exact A4 | flia | flia | flia]. }
    split; [destruct M6 as [hh Hh]; exists hh; unfold FS_HINT0 in *; eapply acellw_frame; [exact Hf | exact Hh | flia | flia | exact A5]|].
    split. { intros i Hi Hni. rewrite (byte_frame M M' rs (fs + 0x8c00 + i) Hf ltac:(flia)); [apply M7; assumption|]. eapply apart_sub; [exact A6 | flia | flia | flia]. }
    split. { eapply shz_frame; [exact Hf | exact M8 | flia | flia |]. replace (SB + (F + 64) / 8)%Z with (SB + F / 8 + 8)%Z; [exact A7|].
             clear PL. Ltac Zify.zify_post_hook ::= Z.div_mod_to_equations. flia. Ltac Zify.zify_post_hook ::= idtac. }
    destruct M9 as [gw Hgw]. exists gw. eapply cell_frame; [exact Hf | exact Hgw | flia | cbn; flia | exact A8].
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  #[local] Abbreviation VALS R FR extra :=
    (junk_vals R ++ fjunk_vals FR ++ junk_vals regs ++ Uw :: Z_to_bv 64 F :: Z_to_bv 64 fa :: Z_to_bv 64 fs :: Z_to_bv 64 n :: extra).

  Definition SFe : expr := EAlu ALU_ADD (EAlu ALU_SRL (EVar 97) (ELit 3)) (ELit SB).
  Definition SF8e : expr := EAlu ALU_ADD (EAlu ALU_SRL (EVar 97) (ELit 3)) (ELit (SB + 8)).

  (* [comment removed for export] *)
  Definition SRB : list expr :=
    sr_upds (sr_vars 0)
      [(2, EVar 96); (9, EVar 96); (8, EVar 66); (3, EVar 67); (4, EVar 68);
       (19, SFe); (21, SF8e); (25, EVar 97); (26, ELit SB); (27, ELit (-8))]%bv.

  Definition KNB : list kentry :=
    [KAlign (EVar 66) 16; KRange (EVar 66) (AS_STKLO + 3584) (2 ^ 47 - 1);
     KAlign (EVar 96) 32; KRange (EVar 96) (AS_STKLO + 3408) (2 ^ 47 - 160); KWr (SA (EVar 96) (-2896)) 2952;
     KWord (SA (EVar 66) (-8)) 8 (EVar 65); KWord (SA (EVar 66) (-16)) 8 (EVar 72);
     KWord (SA (EVar 66) (-24)) 8 (EVar 73); KWord (SA (EVar 66) (-32)) 8 (EVar 82);
     KWord (SA (EVar 66) (-40)) 8 (EVar 83); KWord (SA (EVar 66) (-48)) 8 (EVar 84);
     KWord (SA (EVar 66) (-56)) 8 (EVar 85); KWord (SA (EVar 66) (-64)) 8 (EVar 86);
     KWord (SA (EVar 66) (-72)) 8 (EVar 87); KWord (SA (EVar 66) (-80)) 8 (EVar 88);
     KWord (SA (EVar 66) (-88)) 8 (EVar 89); KWord (SA (EVar 66) (-96)) 8 (EVar 90);
     KWord (SA (EVar 66) (-104)) 8 (EVar 91);
     KDisj (SA (EVar 96) (-2896)) 2952 (SA (EVar 66) (-104)) 104;
     KWord (SA (EVar 96) 24) 8 (EVar 97);
     KAlign (EVar 97) 2048; KRange (EVar 97) 1 (2 ^ 47 - 2048); KWr (SA (EVar 97) 0) 2048;
     KWr (SA (EAlu ALU_SRL (EVar 97) (ELit 3)) SB) 256;
     KZero (SA (EAlu ALU_SRL (EVar 97) (ELit 3)) (SB + 8)) (ELit 122);
     KWord (SA (EVar 97) 2040) 8 (EVar 98); KRange (EVar 98) 1 (2 ^ 47 - 1);
     KRange (EVar 99) 1 (2 ^ 47 - 0xb09000); KRange (EVar 100) 0 (2 ^ 26);
     KWord (SA (ELit 0) GF) 4 (EVar 101); KWr (SA (ELit 0) GF) 4;
     KDisj (SA (EVar 97) 0) 2048 ZSH ZSHL; KDisj (SA (EVar 97) 0) 2048 ZIMG ZIMGL;
     KDisj (SA (EVar 97) 0) 2048 (SA (EVar 96) (-2896)) 2952; KDisj (SA (EVar 97) 0) 2048 (SA (EVar 66) (-104)) 104;
     KDisj (SA (EVar 98) 0) 1 ZSH ZSHL; KDisj (SA (EVar 98) 0) 1 ZIMG ZIMGL;
     KDisj (SA (EVar 98) 0) 1 (SA (EVar 96) (-2896)) 2952; KDisj (SA (EVar 98) 0) 1 (SA (EVar 66) (-104)) 104].
  (* [comment removed for export] *)
  Definition KND : list kentry :=
    if Z.ltb 0 n then [KRange (EAlu ALU_ADD (EVar 74) (EVar 100)) 0 (2 ^ 47 - 2048); KRange (EVar 74) 1 (2 ^ 47 - 2048); KShad (EVar 74) (EVar 100) SB; KBlobD (SA (EVar 74) 0) (EVar 100) 0] else [].

  Lemma packB : forall (R : bvmap 5 word) (FR : bvmap 5 word) (M : word -> option byte) (gw : word) (extra : list word),
    BASE R M -> LibDefs.cell SEGS M GF 4 gw ->
    let E := Env (vals_ev (VALS R FR (gw :: extra))) (blobs_ev [bs]) in
    regs_ok E SRB R /\ fregs_ok E (sfr_vars 32) FR /\ know_ok SEGS E M KNB /\ know_ok SEGS E M KND /\
    regs_ok E (sr_vars 64) regs.
  Proof.
    intros R FR M gw extra (R2 & R9 & R8 & R3 & R4 & R19 & R21 & R25 & R26 & R27 & HMB) Hgw E.
    pose proof HMB as (M1 & M2 & M3 & M4 & M5 & M6 & M7 & M8 & M9).
    need_nums. need_regs. need_wr. pose proof placement as PL.
    pose proof PL as (P0 & P1 & P2 & P3 & P4 & P5 & P6 & P7 & P8 & P9 & P10 & P11 & P12 & P13 & P14 & _). clear PL.
    unfold FS_FRAMES5, FS_FRAMES_LEN, FS_SHFRAMES_LEN, FS_FLAGS5, FS_FLAGS5_LEN, AS_SB in Hwfr5, Hwsf5, Hwfl5.
    pose proof (u64_range sp) as Hspr.
    destruct M1 as (C1 & C2 & C3 & C4 & C5 & C6 & C7 & C8 & C9 & C10 & C11 & C12 & C13).
    unfold cell64, LibDefs.cell, acell in *.
    split; [|split; [|split; [|split]]].
    - unfold SRB, SFe, SF8e. apply regs_ok_pins; [exact (regs_ok_vars [] R _ (blobs_ev [bs]))|].
      repeat (apply Forall_cons; [cbn [fst snd edenot]; ev_simpl E; rewrite_getr; rewrite ?alu_add_lit, ?u_srl3;
                                  first [ reflexivity | assumption | apply (f_equal (Z_to_bv 64)); unfold SB in *; flia
                                        | rewrite u_small by flia; apply (f_equal (Z_to_bv 64)); unfold SB in *; flia ] |]).
      apply Forall_nil.
    - exact (fregs_ok_vars (junk_vals R) FR _ (blobs_ev [bs])).
    - unfold KNB.
      Ltac kwB E0 base w off v val H :=
        eapply (kword_intro SEGS E0 _ (EVar w) base off 8 v val);
        [cbn [edenot]; ev_simpl E0; first [assumption | reflexivity] | cbn [edenot]; ev_simpl E0; reflexivity | flia | flia
        | rewrite ?u_small by flia; flia | change (Z.of_nat 8) with 8%Z; rewrite ?u_small by flia; flia |
         rewrite ?u_small by flia;
         lazymatch goal with |- rdn _ _ (Z_to_bv 64 ?a) _ = _ =>
           lazymatch type of H with rdn _ _ (Z_to_bv 64 ?b) _ = _ => replace a with b by flia; exact H end end].
      constructor; [apply kalign_intro; [flia | cbn [edenot]; ev_simpl E; rewrite Hsp; exact Hal]|].
      constructor; [apply krange_intro; cbn [edenot]; ev_simpl E; rewrite Hsp; flia|].
      constructor; [apply kalign_intro; [flia | cbn [edenot]; ev_simpl E; exact P10]|].
      constructor; [apply krange_intro; cbn [edenot]; ev_simpl E; flia|].
      constructor; [apply (kwr_intro SEGS E M (EVar 96) Uw (-2896) 2952);
                    [cbn [edenot]; ev_simpl E; reflexivity | flia | flia | flia |
                     eapply (proj2 (proj2 (proj2 (writable_at M _ _ ((bv_unsigned Uw) + -2896) 2952 M2 Hstw ltac:(flia) ltac:(flia) ltac:(flia) ltac:(flia) ltac:(flia)))))]|].
      constructor; [kwB E sp 66%nat (-8)%Z (EVar 65) (getr regs 1) C1|].
      constructor; [kwB E sp 66%nat (-16)%Z (EVar 72) (getr regs 8) C2|].
      constructor; [kwB E sp 66%nat (-24)%Z (EVar 73) (getr regs 9) C3|].
      constructor; [kwB E sp 66%nat (-32)%Z (EVar 82) (getr regs 18) C4|].
      constructor; [kwB E sp 66%nat (-40)%Z (EVar 83) (getr regs 19) C5|].
      constructor; [kwB E sp 66%nat (-48)%Z (EVar 84) (getr regs 20) C6|].
      constructor; [kwB E sp 66%nat (-56)%Z (EVar 85) (getr regs 21) C7|].
      constructor; [kwB E sp 66%nat (-64)%Z (EVar 86) (getr regs 22) C8|].
      constructor; [kwB E sp 66%nat (-72)%Z (EVar 87) (getr regs 23) C9|].
      constructor; [kwB E sp 66%nat (-80)%Z (EVar 88) (getr regs 24) C10|].
      constructor; [kwB E sp 66%nat (-88)%Z (EVar 89) (getr regs 25) C11|].
      constructor; [kwB E sp 66%nat (-96)%Z (EVar 90) (getr regs 26) C12|].
      constructor; [kwB E sp 66%nat (-104)%Z (EVar 91) (getr regs 27) C13|].
      constructor; [cbn [kentry_ok]; unfold estart; cbn [a_base a_off edenot]; ev_simpl E; rewrite Hsp; flia|].
      constructor; [kwB E Uw 96%nat 24%Z (EVar 97) (Z_to_bv 64 F) M3|].
      constructor; [apply kalign_intro; [flia | cbn [edenot]; ev_simpl E; rewrite u_small by flia; exact P3]|].
      constructor; [apply krange_intro; cbn [edenot]; ev_simpl E; rewrite u_small by flia; flia|].
      constructor; [apply (kwr_intro SEGS E M (EVar 97) (Z_to_bv 64 F) 0 2048);
                    [cbn [edenot]; ev_simpl E; reflexivity | rewrite u_small by flia; flia | flia | rewrite u_small by flia; flia |
                     rewrite u_small by flia; eapply (proj2 (proj2 (proj2 (writable_at M _ _ (F + 0) 2048 M2 Hwfr5 ltac:(flia) ltac:(flia) ltac:(flia) ltac:(flia) ltac:(flia)))))]|].
      constructor; [replace SB with (SB + 0)%Z at 1 by flia; eapply (kwr_shadow_intro SEGS E M (EVar 97) (Z_to_bv 64 F) 0 256);
                    [cbn [edenot]; ev_simpl E; reflexivity | flia | flia | rewrite u_small by flia; unfold SB in *; flia |
                     rewrite u_small by flia;
                     eapply (proj2 (proj2 (proj2 (writable_at M _ _ (SB + F / 8 + 0) 256 M2 Hwsf5 ltac:(unfold SB; flia) ltac:(unfold SB; flia) ltac:(flia)
                               ltac:(unfold SB; flia) ltac:(unfold SB; flia)))))]|].
      Ltac Zify.zify_post_hook ::= Z.div_mod_to_equations.
      assert (HF64 : ((F + 64) / 8 = F / 8 + 8)%Z) by (clear -P4; flia).
      Ltac Zify.zify_post_hook ::= idtac.
      constructor; [destruct M8 as [_ Hz8];
                    eapply (kzero_shadow_intro SEGS E M (EVar 97) (Z_to_bv 64 F) 8 122);
                    [ cbn [edenot]; ev_simpl E; reflexivity | flia | flia | rewrite u_small by flia; unfold SB in *; flia
                    | rewrite u_small by flia; intros j Hj;
                      replace (SB + F / 8 + j)%Z with (SB + (F + 64) / 8 + (j - 8))%Z by (rewrite HF64; flia);
                      apply Hz8; flia ]|].
      constructor; [kwB E (Z_to_bv 64 F) 97%nat 2040%Z (EVar 98) (Z_to_bv 64 fa) M4|].
      constructor; [apply krange_intro; cbn [edenot]; ev_simpl E; rewrite u_small by flia; flia|].
      constructor; [apply krange_intro; cbn [edenot]; ev_simpl E; rewrite u_small by flia; flia|].
      constructor; [apply krange_intro; cbn [edenot]; ev_simpl E; rewrite u_small by flia; flia|].
      constructor; [eapply (kword_intro SEGS E M (ELit 0) (Z_to_bv 64 0) GF 4 (EVar 101) gw);
                    [reflexivity | cbn [edenot]; ev_simpl E; reflexivity | flia | flia
                    | rewrite u_small by flia; flia | rewrite u_small by flia; cbn; flia
                    | rewrite u_small by flia; exact Hgw]|].
      constructor; [apply (kwr_intro SEGS E M (ELit 0) (Z_to_bv 64 0) GF 4 eq_refl);
                    rewrite ?u_small by flia; cbn [Z.add]; try flia; eapply awritable_frame; [exact M2 | exact Hgfw]|].
      assert (FAPP : appm F 2048) by (apply (app_shrink fs 0xb09000 F 2048 Hfslo); clia).
      assert (FAAPP : appm fa 1) by (apply (app_shrink fs 0xb09000 fa 1 Hfslo); clia).
      assert (FB : (0 <= F)%Z /\ (F + 2048 <= bv_unsigned Uw + -2896)%Z /\ (F + 2048 <= bv_unsigned sp + -104)%Z /\
                   (0 <= fa)%Z /\ (fa + 1 <= bv_unsigned Uw + -2896)%Z /\ (fa + 1 <= bv_unsigned sp + -104)%Z) by clia.
      destruct FB as (FB0 & FB1 & FB2 & FB3 & FB4 & FB5).
      constructor; [eapply kdisj_app_sh; [place_den | rewrite u_small by clia; exact FAPP]|].
      constructor; [eapply kdisj_app_img; [place_den | rewrite u_small by clia; exact FAPP]|].
      constructor; [eapply kdisj_stack; [place_den | place_den | rewrite u_small by clia; exact FB1]|].
      constructor; [eapply kdisj_stack; [place_den | place_den | rewrite u_small by clia; exact FB2]|].
      constructor; [eapply kdisj_app_sh; [place_den | rewrite u_small by clia; exact FAAPP]|].
      constructor; [eapply kdisj_app_img; [place_den | rewrite u_small by clia; exact FAAPP]|].
      constructor; [eapply kdisj_stack; [place_den | place_den | rewrite u_small by clia; exact FB4]|].
      constructor; [eapply kdisj_stack; [place_den | place_den | rewrite u_small by clia; exact FB5]|].
      constructor.
    - unfold KND. destruct (Z.ltb_spec 0 n) as [Hn0|Hn0]; [|constructor].
      destruct (data_bigf M M2 Hn0) as ((HD1 & HD2 & HD3 & HD4) & Hdar). pose proof HD1 as (D1 & D2 & D3 & D4 & D5).
      unfold heapish in HD2. app_facts. pose proof (u64_range data).
      constructor; [eapply krange_add_intro; [place_den | place_den | rewrite ?u_small by flia; flia | flia]|].
      constructor; [apply krange_intro; cbn [edenot]; ev_simpl E; rewrite Ha0; flia|].
      constructor; [eapply (kshad_intro SEGS E M (EVar 74) (EVar 100) data n); [cbn [edenot]; ev_simpl E; exact Ha0 | cbn [edenot]; ev_simpl E; rewrite u_small by flia; reflexivity | flia | flia | exact HD4]|].
      constructor; [|constructor].
      cbn [kentry_ok]. unfold flat, estart, elenZ. cbn [a_base a_off edenot]. ev_simpl E.
      rewrite Ha0. rewrite u_small by flia. split; [flia|]. split; [exact D2|].
      intros i Hi. rewrite Z.add_0_r. apply D5. exact Hi.
    - exact (regs_ok_vars (junk_vals R ++ fjunk_vals FR) regs (Uw :: Z_to_bv 64 F :: Z_to_bv 64 fa :: Z_to_bv 64 fs :: Z_to_bv 64 n :: gw :: extra) (blobs_ev [bs])).
  Qed.

  (* [comment removed for export] *)
  Definition Q (st' : machine_state) : Prop :=
    exists (FPI' : FPState) regs' mem', st' = mkst (FP:=FPI') regs' ret mem' rom /\
      getr regs' 10 = Z_to_bv 64 0 /\
      (forall r, In r fuzz_kept -> getr regs' r = getr regs r) /\
      frame_mod mem mem' BIGF /\
      azero mem' (fs + FS_FLAGS0) FS_FLAGS0_LEN /\ azero mem' (fs + FS_FLAGS5) FS_FLAGS5_LEN.

  Ltac rewrite_getr_in H :=
    repeat match goal with G : getr ?R ?r = _ |- _ => rewrite G in H end.
  Ltac solve_reg := rewrite_getr; rewrite ?alu_add_lit; rewrite ?u_small by flia;
                    rewrite ?Z.add_0_r, ?Z_to_bv_bv_unsigned; first [reflexivity | apply (f_equal (Z_to_bv 64)); flia | idtac].
  Ltac creg r := lazymatch goal with HR : regs_ok _ _ ?R' |- getr ?R' _ = _ => regv HR r; solve_reg end.
  (* [comment removed for export] *)
  Ltac sfreg := rewrite ?alu_add_lit, ?u_srl3; rewrite ?u_small by flia; apply (f_equal (Z_to_bv 64)); unfold SB in *; flia.

  (* [comment removed for export] *)
  Ltac log_frameF RS Hfr :=
    lazymatch goal with
    | EQM : ?M2 = mem_denot ?E2 ?M1 ?log, HLF : log_flat _ _ |- _ =>
      assert (Hfr : frame_mod M1 M2 (regions_denot E2 RS))
        by (rewrite EQM; apply (frame_mod_mem_denot E2 M1 log RS); [exact HLF | flats E2 | vm_compute; reflexivity]);
      unfold regions_denot in Hfr; cbn [map fst snd] in Hfr; unfold adenot in Hfr; cbn [a_base a_off] in Hfr;
      rewrite ?edenot_srl3 in Hfr; cbn [edenot] in Hfr; ev_simpl_in E2 Hfr; unfold v_addi in Hfr;
      rewrite ?u_srl3 in Hfr; rewrite ?u_small in Hfr by flia; clear EQM HLF
    end.

  (* [comment removed for export] *)
  Lemma as_sb_bigf : forall M, frame_mod mem M BIGF -> as_sb SEGS as_asan M.
  Proof.
    intros M Hf. apply (proj2 (as_sb_asan SEGS M)). destruct (as_env_bigf M Hf) as (HC & _).
    pose proof (asan_cells64 SEGS M HC) as (E1 & E2 & _).
    unfold sbcell, cell64, LibDefs.cell. unfold acell in E1, E2. split; [exact E1 | exact E2].
  Qed.

  Lemma curves_pick : forall M off, curves_ok SEGS M data n P -> In off profile_curve_offsets -> curve_ok SEGS M data n (P + off).
  Proof. intros M off HC Hin. unfold curves_ok in HC. rewrite Forall_forall in HC. exact (HC off Hin). Qed.

  (* [comment removed for export] *)
  Lemma MEMB_gf : forall M M', MEMB M -> frame_mod M M' [(Z_to_bv 64 GF, 4%Z)] ->
    (exists gw, LibDefs.cell SEGS M' GF 4 gw) -> MEMB M'.
  Proof.
    intros M M' (M1 & M2 & M3 & M4 & M5 & M6 & M7 & M8 & M9) Hf Hgw.
    need_nums. pose proof placement as PL. hide PL. pose proof (u64_range sp).
    pose proof (unhide PL) as (P1&P2&P3&_&_&_&_&_&P9&_&_&P12&_).
    split; [eapply SAVED13_frame; [exact M1 | exact Hf | solve_apart]|].
    split; [eapply frame_BIGF_app; [exact M2 | exact Hf | apply bincl_of; constructor; [exact in_gfool|constructor]]|].
    split; [eapply cell64_frame; [exact Hf | exact M3 | flia | flia | solve_apart]|].
    split; [eapply acell_frame; [exact Hf | exact M4 | flia | cbn; flia | solve_apart]|].
    split. { intros i Hi Hni. unfold FS_FLAGS0, FS_FLAGS0_LEN in *. rewrite (byte_frame M M' _ (fs + 4096 + i) Hf ltac:(flia)); [apply M5; assumption|]. solve_apart. }
    split; [destruct M6 as [hh Hh]; exists hh; unfold FS_HINT0 in *; eapply acellw_frame; [exact Hf | exact Hh | flia | flia | solve_apart]|].
    split. { intros i Hi Hni. rewrite (byte_frame M M' _ (fs + 0x8c00 + i) Hf ltac:(flia)); [apply M7; assumption|]. solve_apart. }
    split; [| exact Hgw].
    eapply shz_frame; [exact Hf | exact M8 | flia | flia | unfold SB; try solve_apart].
    all: clear PL. Ltac Zify.zify_post_hook ::= Z.div_mod_to_equations. all: flia. Ltac Zify.zify_post_hook ::= idtac.
  Qed.

  (* [comment removed for export] *)
  Lemma after_rte : forall M M', MEMB M -> parsed_ok SEGS M data n bs P ->
    frame_mod M M' [(Z_to_bv 64 (bv_unsigned Uw - 16), 16%Z)] -> MEMB M' /\ parsed_ok SEGS M' data n bs P.
  Proof.
    intros M M' HM HP Hf. need_nums. pose proof placement as PL. hide PL. pose proof (u64_range sp).
    pose proof (unhide PL) as (P1&P2&P3&_&_&_&_&_&P9&_&_&P12&_).
    split.
    - eapply MEMB_frame; [exact HM | exact Hf | apply bincl_of; constructor; [cbn [fst snd]; apply in_stack; flia|constructor] |..];
        unfold SB; try solve_apart.
      all: clear PL. Ltac Zify.zify_post_hook ::= Z.div_mod_to_equations. all: flia. Ltac Zify.zify_post_hook ::= idtac.
    - eapply parsed_ok_frame; [exact Hf | exact HP | flia | flia | solve_apart | solve_apart | solve_apart].
  Qed.

  (* [comment removed for export] *)
  Definition A2BF (M : word -> option byte) (ic : Z) (gps : list Z) (g8 g16 : word) : Prop :=
    cell32 SEGS M (P + 304) ic /\ cell32 SEGS M (P + 460) 3 /\ cell64 SEGS M (P + 288) g8 /\ cell64 SEGS M (P + 296) g16 /\
    cell8 SEGS M (P + 966) 1 /\ (forall i, (0 <= i < ic)%Z -> cell8 SEGS M (P + 308 + i) (nth (Z.to_nat i) gps 0%Z)).
  Lemma A2BF_rte : forall M M' ic gps g8 g16, A2BF M ic gps g8 g16 -> (0 <= ic <= 4)%Z ->
    frame_mod M M' [(Z_to_bv 64 (bv_unsigned Uw - 16), 16%Z)] -> A2BF M' ic gps g8 g16.
  Proof.
    intros M M' ic gps g8 g16 (A1 & A2 & A3 & A4 & A5 & A6) Hic Hf. need_nums. pose proof placement as PL. hide PL. pose proof (u64_range sp).
    pose proof (unhide PL) as (P1&P2&P3&_&_&_&_&_&P9&_&_&P12&_). clear PL.
    split; [eapply cell32_frame; [exact Hf | exact A1 | flia | flia | solve_apart]|].
    split; [eapply cell32_frame; [exact Hf | exact A2 | flia | flia | solve_apart]|].
    split; [eapply cell64_frame; [exact Hf | exact A3 | flia | flia | solve_apart]|].
    split; [eapply cell64_frame; [exact Hf | exact A4 | flia | flia | solve_apart]|].
    split; [eapply cell8_frame; [exact Hf | exact A5 | flia | flia | solve_apart]|].
    intros i Hi. eapply cell8_frame; [exact Hf | exact (A6 i Hi) | flia | flia | solve_apart].
  Qed.

  (* [comment removed for export] *)
  Ltac call_rte RET OFF :=
    lazymatch goal with |- runs_to _ (@mkst ?I ?R' _ ?M' _) _ =>
    lazymatch goal with HR : regs_ok _ _ R', HMB : MEMB M', HP : parsed_ok _ M' _ _ _ _, Hn0 : (0 < n)%Z |- _ =>
      eapply rt_call;
      [ eapply (Hrte data n bs (Z_to_bv 64 (P + OFF)) I R' M' rom (Z_to_bv 64 RET));
        [ regv HR (1%bv:reg); reflexivity
        | apply ret_ok_even; rewrite u_small by flia; reflexivity
        | unfold rte_pre_as; cbn [al_abi as_asan]; rewrite !u_small by flia; pose proof HMB as (_ & ?HM2 & _ & _ & _ & _ & _ & ?HM8 & _);
          split; [regv HR (10%bv:reg); rewrite_getr; rewrite ?alu_add_lit; rewrite ?u_small by flia; apply (f_equal (Z_to_bv 64)); flia|];
          split; [exact (proj1 (data_bigf M' HM2 Hn0))|];
          split; [apply (curves_pick M' OFF); [pose proof HP as (? & ? & ? & ? & _ & _ & _ & _ & ?HC & _); exact HC | in_lit]|];
          split; [replace (F + 64 + OFF)%Z with (F + (64 + OFF))%Z by flia; apply F8k; reflexivity|];
          split; [unfold heapish; plc|];
          split; [eapply (shz_sub M' _ _ _ _ HM8); [replace (F + 64 + OFF)%Z with (F + (64 + OFF))%Z by flia; apply F8k; reflexivity | flia | flia | flia]|];
          split; [exact (as_sb_bigf M' HM2)|];
          exists Uw; split; [regv HR (2%bv:reg); reflexivity|];
          unfold as_frame, stackish; split; [flia|]; split; [apply (mod_down (bv_unsigned Uw) 16 2); [flia|flia|assumption]|];
          eapply (writable_at M' _ _ (bv_unsigned Uw - 16) 16 HM2 (Hstw HALL)); flia ]
      | cbv beta;
        let FPI' := fresh "FPI" in let regs' := fresh "R" in let mem' := fresh "MC" in
        let Hkeep := fresh "Hkeep" in let Hfkeep := fresh "Hfkeep" in let Hfr := fresh "Hfr" in let HX := fresh "HX2" in
        intros FPI' regs' mem' (Hkeep & Hfkeep & Hfr); unfold rte_post_as in Hfr;
        assert (HX : getr R' 2 = Uw) by (regv HR (2%bv:reg); reflexivity); rewrite HX in Hfr; clear HX;
        unfold regs_kept in Hkeep; unfold fregs_kept in Hfkeep;
        after_call Hkeep Hfkeep FPI'; clear Hkeep Hfkeep;
        lazymatch goal with HK : know_ok _ _ _ _ |- _ => kframe HK Hfr [(SA (EVar 96) (-16), 16%Z)] end;
        let HMB' := fresh "HMB" in let HP' := fresh "HP" in
        destruct (after_rte M' mem' HMB HP Hfr) as [HMB' HP'];
        try (lazymatch goal with HA : A2BF M' _ _ _ _ |- _ =>
               let HA' := fresh "HA" in pose proof (A2BF_rte _ _ _ _ _ _ HA ltac:(flia) Hfr) as HA'; clear HA; rename HA' into HA end);
        clear Hfr HMB HP; rename HMB' into HMB; rename HP' into HP ]
    end end.

  (* [comment removed for export] *)
  Ltac call_rte_auto RET :=
    lazymatch goal with HR : regs_ok _ ?sr _ |- runs_to _ _ _ =>
      lazymatch eval vm_compute in (sr_get sr 10%bv) with
      | EAlu ALU_ADD (EVar 97) (ELit ?k) => let OFF := eval vm_compute in (k - 64)%Z in call_rte RET OFF
      end end.

  (* [comment removed for export] *)
  Ltac base_now H64i :=
    lazymatch goal with |- BASE ?R' ?M' =>
    lazymatch goal with HR : regs_ok ?E ?sr R', HMB : MEMB M' |- _ =>
      split; [regv HR (2%bv:reg); reflexivity|];
      split; [regv HR (9%bv:reg); reflexivity|];
      split; [regv HR (8%bv:reg); rewrite_getr; reflexivity|];
      split; [regv HR (3%bv:reg); reflexivity|];
      split; [regv HR (4%bv:reg); reflexivity|];
      split; [regv HR (19%bv:reg); sfreg|];
      split; [regv HR (21%bv:reg); sfreg|];
      split; [regv HR (25%bv:reg); reflexivity|];
      split; [regv HR (26%bv:reg); reflexivity|];
      split; [regv HR (27%bv:reg); reflexivity|];
      exact HMB
    end end.
End Proof.
