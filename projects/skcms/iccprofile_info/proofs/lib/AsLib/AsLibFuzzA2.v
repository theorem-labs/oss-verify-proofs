(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
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
Ltac Zify.zify_post_hook ::= Z.div_mod_to_equations.
Ltac Zify.zify_post_hook ::= idtac.

From OSSVerify.Proofs.skcms.iccprofile_info.lib.AsLib Require Import AsLibFuzzADefs.
From OSSVerify.Proofs.skcms.iccprofile_info.lib.AsLib Require AsLibFuzzAHdr.
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
#[local] Abbreviation realign160 := AsLibFuzzAHdr.realign160.
#[local] Abbreviation gfool_apart := AsLibFuzzAHdr.gfool_apart.

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
  #[local] Abbreviation pos := (AsLibFuzzAHdr.pos h5).
  #[local] Abbreviation F := (AsLibFuzzAHdr.F fs h5).
  #[local] Abbreviation fa := (AsLibFuzzAHdr.fa fs h5).
  #[local] Abbreviation Uw := (AsLibFuzzAHdr.Uw sp).
  #[local] Abbreviation F_eq := (AsLibFuzzAHdr.F_eq fs h5).
  #[local] Abbreviation fa_eq := (AsLibFuzzAHdr.fa_eq fs h5).
  #[local] Abbreviation pos_eq := (AsLibFuzzAHdr.pos_eq h5).
  #[local] Abbreviation placement := (AsLibFuzzAHdr.placement ceil regs mem ret sp data n bs fs h0 h5 ctx thr t48 t56 dtls v24 HALL).
  #[local] Abbreviation F8k := (AsLibFuzzAHdr.F8k ceil regs mem ret sp data n bs fs h0 h5 ctx thr t48 t56 dtls v24 HALL).
  #[local] Abbreviation nums_zone := (AsLibFuzzAHdr.nums_zone ceil regs mem ret sp data n bs fs h0 h5 ctx thr t48 t56 dtls v24 HALL).
  #[local] Abbreviation BIGF := (AsLibFuzzAHdr.BIGF sp fs).
  #[local] Abbreviation in_bigf := (AsLibFuzzAHdr.in_bigf sp fs).
  #[local] Abbreviation bincl_of := (AsLibFuzzAHdr.bincl_of sp fs).
  #[local] Abbreviation frame_BIGF_app := (AsLibFuzzAHdr.frame_BIGF_app ceil regs mem ret sp data n bs fs h0 h5 ctx thr t48 t56 dtls v24 HALL).
  #[local] Abbreviation in_stack := (AsLibFuzzAHdr.in_stack ceil regs mem ret sp data n bs fs h0 h5 ctx thr t48 t56 dtls v24 HALL).
  #[local] Abbreviation in_gfool := (AsLibFuzzAHdr.in_gfool ceil regs mem ret sp data n bs fs h0 h5 ctx thr t48 t56 dtls v24 HALL).
  #[local] Abbreviation in_hint0 := (AsLibFuzzAHdr.in_hint0 ceil regs mem ret sp data n bs fs h0 h5 ctx thr t48 t56 dtls v24 HALL).
  #[local] Abbreviation in_hint5 := (AsLibFuzzAHdr.in_hint5 ceil regs mem ret sp data n bs fs h0 h5 ctx thr t48 t56 dtls v24 HALL).
  #[local] Abbreviation in_flags0 := (AsLibFuzzAHdr.in_flags0 ceil regs mem ret sp data n bs fs h0 h5 ctx thr t48 t56 dtls v24 HALL).
  #[local] Abbreviation in_flags5 := (AsLibFuzzAHdr.in_flags5 ceil regs mem ret sp data n bs fs h0 h5 ctx thr t48 t56 dtls v24 HALL).
  #[local] Abbreviation in_frames0 := (AsLibFuzzAHdr.in_frames0 ceil regs mem ret sp data n bs fs h0 h5 ctx thr t48 t56 dtls v24 HALL).
  #[local] Abbreviation in_frames5 := (AsLibFuzzAHdr.in_frames5 ceil regs mem ret sp data n bs fs h0 h5 ctx thr t48 t56 dtls v24 HALL).
  #[local] Abbreviation in_shframes0 := (AsLibFuzzAHdr.in_shframes0 ceil regs mem rom ret sp data n bs fs h0 h5 ctx thr t48 t56 dtls v24 HALL).
  #[local] Abbreviation in_shframes5 := (AsLibFuzzAHdr.in_shframes5 ceil regs mem rom ret sp data n bs fs h0 h5 ctx thr t48 t56 dtls v24 HALL).
  #[local] Abbreviation apart_env_bigf := (AsLibFuzzAHdr.apart_env_bigf ceil regs mem rom ret sp data n bs fs h0 h5 ctx thr t48 t56 dtls v24 HALL).
  #[local] Abbreviation apart_heap_bigf := (AsLibFuzzAHdr.apart_heap_bigf ceil regs mem rom ret sp data n bs fs h0 h5 ctx thr t48 t56 dtls v24 HALL).
  #[local] Abbreviation apart_data_bigf := (AsLibFuzzAHdr.apart_data_bigf ceil regs mem rom ret sp data n bs fs h0 h5 ctx thr t48 t56 dtls v24 HALL).
  #[local] Abbreviation apart_stsh_bigf := (AsLibFuzzAHdr.apart_stsh_bigf ceil regs mem rom ret sp data n bs fs h0 h5 ctx thr t48 t56 dtls v24 HALL).
  #[local] Abbreviation apart_hdr_bigf := (AsLibFuzzAHdr.apart_hdr_bigf ceil regs mem rom ret sp data n bs fs h0 h5 ctx thr t48 t56 dtls v24 HALL).
  #[local] Abbreviation as_env_bigf := (AsLibFuzzAHdr.as_env_bigf ceil regs mem rom ret sp data n bs fs h0 h5 ctx thr t48 t56 dtls v24 HALL).
  #[local] Abbreviation fs_hdr_bigf := (AsLibFuzzAHdr.fs_hdr_bigf ceil regs mem rom ret sp data n bs fs h0 h5 ctx thr t48 t56 dtls v24 HALL).
  #[local] Abbreviation fs_writable_bigf := (AsLibFuzzAHdr.fs_writable_bigf ceil regs mem ret sp data n bs fs h0 h5 ctx thr t48 t56 dtls v24 HALL).
  #[local] Abbreviation data_bigf := (AsLibFuzzAHdr.data_bigf ceil regs mem rom ret sp data n bs fs h0 h5 ctx thr t48 t56 dtls v24 HALL).
  #[local] Abbreviation stsh_bigf := (AsLibFuzzAHdr.stsh_bigf ceil regs mem rom ret sp data n bs fs h0 h5 ctx thr t48 t56 dtls v24 HALL).
  #[local] Abbreviation writable_at := (AsLibFuzzAHdr.writable_at mem sp fs).
  #[local] Abbreviation SAVED13 := (AsLibFuzzAHdr.SAVED13 regs sp).
  #[local] Abbreviation flags5_but := (AsLibFuzzAHdr.flags5_but fs h5).
  #[local] Abbreviation MEMB := (AsLibFuzzAHdr.MEMB regs mem sp fs h5).
  #[local] Abbreviation BASE := (AsLibFuzzAHdr.BASE regs mem sp fs h5).
  #[local] Abbreviation SAVED13_frame := (AsLibFuzzAHdr.SAVED13_frame ceil regs mem ret sp data n bs fs h0 h5 ctx thr t48 t56 dtls v24 HALL).
  #[local] Abbreviation MEMB_frame := (AsLibFuzzAHdr.MEMB_frame ceil regs mem ret sp data n bs fs h0 h5 ctx thr t48 t56 dtls v24 HALL).
  #[local] Abbreviation SFe := AsLibFuzzAHdr.SFe.
  #[local] Abbreviation SF8e := AsLibFuzzAHdr.SF8e.
  #[local] Abbreviation SRB := AsLibFuzzAHdr.SRB.
  #[local] Abbreviation KNB := AsLibFuzzAHdr.KNB.
  #[local] Abbreviation KND := (AsLibFuzzAHdr.KND n).
  #[local] Abbreviation packB := (AsLibFuzzAHdr.packB ceil regs mem rom ret sp data n bs fs h0 h5 ctx thr t48 t56 dtls v24 HALL).
  #[local] Abbreviation Q := (AsLibFuzzAHdr.Q regs mem rom ret sp fs).
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
  #[local] Notation P := (F + 64)%Z.
  #[local] Notation T := (F + 1168)%Z.
  #[local] Notation SF := (SB + F / 8)%Z.
  #[local] Abbreviation s := (bv_unsigned sp).
  Ltac Zify.zify_post_hook ::= Z.div_mod_to_equations.
  Ltac Zify.zify_post_hook ::= idtac.
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
  #[local] Opaque AsLibFuzzAHdr.Uw.
  Ltac Zify.zify_post_hook ::= Z.div_mod_to_equations.
  Ltac Zify.zify_post_hook ::= idtac.
  Ltac Zify.zify_post_hook ::= Z.div_mod_to_equations.
  Ltac lia1 := first [ clia | match goal with H : _ \/ _ |- _ => (destruct H as [H|H]; clia) end ].
  Ltac lia2 := first [ lia1 | match goal with H : _ \/ _ |- _ => (destruct H as [H|H]; lia1) end ].
  Ltac zlia := unfold in_env_zone, AS_IMGLO, AS_IMGHI, AS_SIMGLO, AS_SIMGHI in *; cbn -[Z.div]; flia.
  Ltac Zify.zify_post_hook ::= idtac.
  Ltac Zify.zify_post_hook ::= Z.div_mod_to_equations.
  Ltac Zify.zify_post_hook ::= idtac.
  Ltac Zify.zify_post_hook ::= Z.div_mod_to_equations.
  Ltac Zify.zify_post_hook ::= idtac.
  Ltac Zify.zify_post_hook ::= Z.div_mod_to_equations.
  Ltac Zify.zify_post_hook ::= idtac.
  Ltac Zify.zify_post_hook ::= Z.div_mod_to_equations.
  Ltac Zify.zify_post_hook ::= idtac.
  Ltac Zify.zify_post_hook ::= Z.div_mod_to_equations.
  Ltac Zify.zify_post_hook ::= idtac.
  #[local] Abbreviation VALS R FR extra :=
    (junk_vals R ++ fjunk_vals FR ++ junk_vals regs ++ Uw :: Z_to_bv 64 F :: Z_to_bv 64 fa :: Z_to_bv 64 fs :: Z_to_bv 64 n :: extra).
  Ltac Zify.zify_post_hook ::= Z.div_mod_to_equations.
  Ltac Zify.zify_post_hook ::= idtac.
  Ltac rewrite_getr_in H :=
    repeat match goal with G : getr ?R ?r = _ |- _ => rewrite G in H end.
  Ltac solve_reg := rewrite_getr; rewrite ?alu_add_lit; rewrite ?u_small by flia;
                    rewrite ?Z.add_0_r, ?Z_to_bv_bv_unsigned; first [reflexivity | apply (f_equal (Z_to_bv 64)); flia | idtac].
  Ltac creg r := lazymatch goal with HR : regs_ok _ _ ?R' |- getr ?R' _ = _ => regv HR r; solve_reg end.
  Ltac sfreg := rewrite ?alu_add_lit, ?u_srl3; rewrite ?u_small by flia; apply (f_equal (Z_to_bv 64)); unfold SB in *; flia.
  Ltac log_frameF RS Hfr :=
    lazymatch goal with
    | EQM : ?M2 = mem_denot ?E2 ?M1 ?log, HLF : log_flat _ _ |- _ =>
      assert (Hfr : frame_mod M1 M2 (regions_denot E2 RS))
        by (rewrite EQM; apply (frame_mod_mem_denot E2 M1 log RS); [exact HLF | flats E2 | vm_compute; reflexivity]);
      unfold regions_denot in Hfr; cbn [map fst snd] in Hfr; unfold adenot in Hfr; cbn [a_base a_off] in Hfr;
      rewrite ?edenot_srl3 in Hfr; cbn [edenot] in Hfr; ev_simpl_in E2 Hfr; unfold v_addi in Hfr;
      rewrite ?u_srl3 in Hfr; rewrite ?u_small in Hfr by flia; clear EQM HLF
    end.
  Ltac sc_lia ::= first [ nlia | clia | dlia ].


  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Hypothesis phaseE : forall (FPX : FPState) R M, BASE R M ->
    runs_to SEGS (mkst (FP:=FPX) R (Z_to_bv 64 0x80274) M rom) Q.
  (* [comment removed for export] *)
  #[local] Abbreviation as_sb_bigf := (AsLibFuzzAHdr.as_sb_bigf ceil regs mem rom ret sp data n bs fs h0 h5 ctx thr t48 t56 dtls v24 HALL).
  #[local] Abbreviation curves_pick := (AsLibFuzzAHdr.curves_pick data n fs h5).
  #[local] Abbreviation MEMB_gf := (AsLibFuzzAHdr.MEMB_gf ceil regs mem ret sp data n bs fs h0 h5 ctx thr t48 t56 dtls v24 HALL).
  #[local] Abbreviation after_rte := (AsLibFuzzAHdr.after_rte ceil regs mem ret sp data n bs fs h0 h5 ctx thr t48 t56 dtls v24 HALL).
  #[local] Abbreviation A2BF := (AsLibFuzzAHdr.A2BF fs h5).
  #[local] Abbreviation A2BF_rte := (AsLibFuzzAHdr.A2BF_rte ceil regs mem ret sp data n bs fs h0 h5 ctx thr t48 t56 dtls v24 HALL).
  Ltac Zify.zify_post_hook ::= Z.div_mod_to_equations.
  Ltac Zify.zify_post_hook ::= idtac.
  Ltac Zify.zify_post_hook ::= Z.div_mod_to_equations.
  Ltac Zify.zify_post_hook ::= idtac.
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
  Ltac call_rte_auto RET :=
    lazymatch goal with HR : regs_ok _ ?sr _ |- runs_to _ _ _ =>
      lazymatch eval vm_compute in (sr_get sr 10%bv) with
      | EAlu ALU_ADD (EVar 97) (ELit ?k) => let OFF := eval vm_compute in (k - 64)%Z in call_rte RET OFF
      end end.
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


  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Hypothesis phaseC : forall (FPX : FPState) R M, BASE R M ->
    getr R 20 = Z_to_bv 64 P -> (0 < n)%Z ->
    parsed_ok SEGS M data n bs P -> cell32 SEGS M (P + 460) 3 ->
    runs_to SEGS (mkst (FP:=FPX) R (Z_to_bv 64 0x80228) M rom) Q.

  (* [comment removed for export] *)
  Lemma KND_pos : (0 < n)%Z -> KND = [KRange (EAlu ALU_ADD (EVar 74) (EVar 100)) 0 (2 ^ 47 - 2048); KRange (EVar 74) 1 (2 ^ 47 - 2048); KShad (EVar 74) (EVar 100) SB; KBlobD (SA (EVar 74) 0) (EVar 100) 0].
  Proof. intros Hn0. unfold KND. destruct (Z.ltb_spec 0 n); [reflexivity | exfalso; flia]. Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Hypothesis phaseB2 : forall (FPX : FPState) R M (g8 g16 : word) (G : Z), BASE R M ->
    getr R 20 = Z_to_bv 64 P -> getr R 12 = Z_to_bv 64 G -> (0 < n)%Z ->
    parsed_ok SEGS M data n bs P -> cell32 SEGS M (P + 460) 3 ->
    cell64 SEGS M (P + 288) g8 -> cell64 SEGS M (P + 296) g16 ->
    (bv_unsigned g8 <> 0%Z -> inDATA data n (bv_unsigned g8) G) ->
    (bv_unsigned g16 <> 0%Z -> inDATA data n (bv_unsigned g16) (2 * G)) ->
    (1 <= G <= 12684751875)%Z ->
    runs_to SEGS (mkst (FP:=FPX) R (Z_to_bv 64 0x8019c) M rom) Q.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma zprod_bounds : forall gps, Forall (fun g => 2 <= g <= 255)%Z gps ->
    (1 <= zprod gps <= 255 ^ Z.of_nat (length gps))%Z.
  Proof.
    intros gps H. induction H as [|g gps Hg H IH]; [cbn; flia|].
    cbn [zprod length]. rewrite Nat2Z.inj_succ, Z.pow_succ_r by flia. nia.
  Qed.

  (* [comment removed for export] *)
  Definition KGP (o : Z) (i : nat) : list kentry := [KWord (SA (EVar 97) o) 1 (EVar i); KRange (EVar i) 2 255].
  Definition KGPS (k : nat) : list kentry :=
    match k with
    | 0 => []
    | 1 => KGP 372 104
    | 2 => KGP 372 104 ++ KGP 373 105
    | 3 => KGP 372 104 ++ KGP 373 105 ++ KGP 374 106
    | _ => KGP 372 104 ++ KGP 373 105 ++ KGP 374 106 ++ KGP 375 107
    end%nat.
  Definition KNA2B (k : nat) : list kentry :=
    KWord (SA (EVar 97) 1030) 1 (ELit 1) :: KWord (SA (EVar 97) 368) 4 (ELit (Z.of_nat k)) ::
    KWord (SA (EVar 97) 524) 4 (ELit 3) :: KWord (SA (EVar 97) 352) 8 (EVar 102) :: KWord (SA (EVar 97) 360) 8 (EVar 103) ::
    KGPS k ++ KNB ++ [KRange (EAlu ALU_ADD (EVar 74) (EVar 100)) 0 (2 ^ 47 - 2048); KRange (EVar 74) 1 (2 ^ 47 - 2048); KShad (EVar 74) (EVar 100) SB; KBlobD (SA (EVar 74) 0) (EVar 100) 0].

  (* [comment removed for export] *)
  Lemma mul3_word : forall a b : Z, (0 <= a < 2 ^ 64)%Z -> (0 <= b < 2 ^ 64)%Z ->
    mul_div M_MUL (Z_to_bv 64 a) (Z_to_bv 64 b) = Z_to_bv 64 (a * b).
  Proof.
    intros a b Ha Hb. rewrite m_mul. unfold v_mul. rewrite !u_small by flia. reflexivity.
  Qed.

  (* [comment removed for export] *)
  Lemma gp_mul2 : forall a b la ua lb ub : Z, (0 <= la <= a)%Z -> (a <= ua)%Z -> (0 <= lb <= b)%Z -> (b <= ub)%Z -> (la * lb <= a * b <= ua * ub)%Z.
  Proof. intros a b la ua lb ub Ha1 Ha2 Hb1 Hb2. split; apply Z.mul_le_mono_nonneg; lia. Qed.
  Lemma gp_b1 : forall a, (2 <= a <= 255)%Z -> (1 <= 3 * (a * 1) <= 12684751875)%Z.
  Proof. intros a Ha. lia. Qed.
  Lemma gp_b2 : forall a b, (2 <= a <= 255)%Z -> (2 <= b <= 255)%Z -> (1 <= 3 * (a * (b * 1)) <= 12684751875)%Z.
  Proof. intros a b Ha Hb. rewrite Z.mul_1_r. pose proof (gp_mul2 a b 2 255 2 255 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)) as H. lia. Qed.
  Lemma gp_b3 : forall a b c, (2 <= a <= 255)%Z -> (2 <= b <= 255)%Z -> (2 <= c <= 255)%Z -> (1 <= 3 * (a * (b * (c * 1))) <= 12684751875)%Z.
  Proof.
    intros a b c Ha Hb Hc. rewrite Z.mul_1_r. pose proof (gp_mul2 b c 2 255 2 255 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)) as H.
    pose proof (gp_mul2 a (b * c) 2 255 (2 * 2) (255 * 255) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)) as H2. lia.
  Qed.
  Lemma gp_b4 : forall a b c d, (2 <= a <= 255)%Z -> (2 <= b <= 255)%Z -> (2 <= c <= 255)%Z -> (2 <= d <= 255)%Z ->
    (1 <= 3 * (a * (b * (c * (d * 1)))) <= 12684751875)%Z.
  Proof.
    intros a b c d Ha Hb Hc Hd. rewrite Z.mul_1_r. pose proof (gp_mul2 c d 2 255 2 255 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)) as H.
    pose proof (gp_mul2 b (c * d) 2 255 (2 * 2) (255 * 255) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)) as H2.
    pose proof (gp_mul2 a (b * (c * d)) 2 255 (2 * (2 * 2)) (255 * (255 * 255)) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)) as H3. lia.
  Qed.
  Lemma gp_m1 : forall a, (2 <= a <= 255)%Z -> (0 <= 3 * a < 2 ^ 64)%Z.
  Proof. intros a Ha. lia. Qed.
  Lemma gp_m2 : forall a b, (2 <= a <= 255)%Z -> (2 <= b <= 255)%Z -> (0 <= 3 * a * b < 2 ^ 64)%Z.
  Proof. intros a b Ha Hb. pose proof (gp_mul2 a b 2 255 2 255 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)) as H. lia. Qed.
  Lemma gp_m3 : forall a b c, (2 <= a <= 255)%Z -> (2 <= b <= 255)%Z -> (2 <= c <= 255)%Z -> (0 <= 3 * a * b * c < 2 ^ 64)%Z.
  Proof.
    intros a b c Ha Hb Hc. pose proof (gp_mul2 a b 2 255 2 255 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)) as H.
    pose proof (gp_mul2 (a * b) c (2 * 2) (255 * 255) 2 255 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)) as H2. lia.
  Qed.

  Lemma phaseB : forall (FPX : FPState) R M, BASE R M ->
    getr R 20 = Z_to_bv 64 P ->
    parsed_ok SEGS M data n bs P ->
    runs_to SEGS (mkst (FP:=FPX) R (Z_to_bv 64 0x80124) M rom) Q.
  Proof.
    intros FPX R M HB R20 HP. pose proof HB as (R2 & R9 & R8 & R3 & R4 & R19 & R21 & R25 & R26 & R27 & HMB).
    pose proof HMB as (_ & HM2 & _ & _ & _ & _ & _ & _ & [gw Hgw]).
    need_nums. need_regs. pose proof placement as PL.
    pose proof PL as (P0 & P1 & P2 & P3 & P4 & P5 & P6 & P7 & P8 & P9 & P10 & P11 & P12 & P13 & P14 & _). clear PL.
    pose proof (u64_range sp) as Hspr. pose proof (u64_range data) as Hdr.
    pose proof HP as (psz & tc & htrc & hasA2B & _ & _ & _ & Htags & _ & _ & _ & [Hh1 H966] & Hha & Hgrid).
    (* [comment removed for export] *)
    assert (Hn0 : (0 < n)%Z) by (destruct Htags as (Ht0 & Ht & _); flia).
    destruct (data_bigf M HM2 Hn0) as ((HD1 & HD2 & HD3 & HD4) & Hdar). pose proof HD1 as (D1 & D2 & D3 & D4 & D5).
    unfold heapish in HD2. app_facts. clear HM2.
    unfold LibDefs.cell in H966.
    destruct Hha as [Hha | Hha]; rewrite Hha in H966.
    { (* [comment removed for export] *)
      destruct (packB R (fp_regs (FPState:=FPX)) M gw [] HB Hgw) as (HR & HF & HKB & _ & H64).
      pose proof (H64 : id _) as H64i. clear H64. unfold KNB in HKB.
      apply (regs_ok_pin _ _ R 20 (EAlu ALU_ADD (EVar 97) (ELit 64))) in HR;
        [| cbn [edenot]; ev_simpl_goal; rewrite alu_add_lit, u_small by flia; rewrite R20; apply (f_equal (Z_to_bv 64)); flia].
      lazymatch type of HR with regs_ok ?E _ _ =>
        assert (HK : know_ok SEGS E M (KWord (SA (EVar 97) 1030) 1 (ELit 0) :: KNB));
        [ constructor; [| exact HKB];
          eapply (kword_intro SEGS E M (EVar 97) (Z_to_bv 64 F) 1030 1 (ELit 0) (Z_to_bv 64 0));
            [cbn [edenot]; ev_simpl E; reflexivity | reflexivity | flia | flia | rewrite u_small by flia; flia | rewrite u_small by flia; cbn; flia |
             rewrite u_small by flia; replace (F + 1030)%Z with (F + 64 + 966)%Z by flia; exact H966]
        | clear HKB; unfold KNB in HK ] end.
      run_fp 100%nat [0x80274%Z] noscr false. apply phaseE. base_now H64i. }
    (* [comment removed for export] *)
    destruct (Hgrid ltac:(rewrite Hha; flia)) as (ic & oc & gps & g8 & g16 & Hic & Hoc & Hicr & Hlen & Hgps & Hgp & Hg8 & Hg16 & Hoc3 & Hin).
    subst oc.
    pose proof (zprod_bounds gps Hgps) as HZP.
    pose proof (u64_range g8) as Hg8r. pose proof (u64_range g16) as Hg16r.
    rewrite Forall_forall in Hgps.
    assert (HA : A2BF M ic gps g8 g16).
    { split; [replace (P + 304)%Z with (P + 160 + 144)%Z by flia; exact Hic|].
      split; [replace (P + 460)%Z with (P + 160 + 300)%Z by flia; exact Hoc|].
      split; [replace (P + 288)%Z with (P + 160 + 128)%Z by flia; exact Hg8|].
      split; [replace (P + 296)%Z with (P + 160 + 136)%Z by flia; exact Hg16|].
      split; [split; [flia | exact H966]|].
      intros i Hi. replace (P + 308 + i)%Z with (P + 160 + 148 + i)%Z by flia. apply Hgp. exact Hi. }
    clear Hic Hoc Hg8 Hg16 Hgp H966 Hh1.
    (* [comment removed for export] *)
    Ltac kwP E0 M0 off w v val H :=
      eapply (kword_intro SEGS E0 M0 (EVar 97) (Z_to_bv 64 F) off w v val);
        [cbn [edenot]; ev_simpl E0; reflexivity | cbn [edenot]; ev_simpl E0; reflexivity | flia | flia
        | rewrite u_small by flia; flia | rewrite u_small by flia; cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; flia
        | rewrite u_small by flia;
          lazymatch type of H with rdn _ _ (Z_to_bv 64 ?b) _ = _ => replace (F + off)%Z with b by flia; exact H end].
    Ltac caseB EXTRA HA Hlen HB Hgw R20 :=
      lazymatch goal with |- runs_to _ (@mkst ?FPX ?R _ ?M _) _ =>
      destruct (packB R (fp_regs (FPState:=FPX)) M _ EXTRA HB Hgw) as (HR & HF & HKB & HKD & H64);
      pose proof (H64 : id _) as H64i; clear H64;
      lazymatch goal with Hn0 : (0 < n)%Z |- _ => rewrite (KND_pos Hn0) in HKD end;
      apply (regs_ok_pin _ _ R 20 (EAlu ALU_ADD (EVar 97) (ELit 64))) in HR;
        [| cbn [edenot]; ev_simpl_goal; rewrite alu_add_lit, u_small by flia; rewrite R20; apply (f_equal (Z_to_bv 64)); flia];
      pose proof HA as (?Hic & ?Hoc & ?Hg8 & ?Hg16 & [_ ?H966] & ?Hgp);
      unfold cell32, cell64, LibDefs.cell in Hic, Hoc, Hg8, Hg16, H966; destruct Hic as [_ Hic]; destruct Hoc as [_ Hoc];
      lazymatch type of HA with A2BF _ _ ?gps ?g8 ?g16 =>
      lazymatch type of HR with regs_ok ?E _ _ =>
      lazymatch type of Hlen with Z.of_nat ?k = _ =>
        assert (HK : know_ok SEGS E M (KNA2B k));
        [ unfold KNA2B;
          constructor; [kwP E M 1030%Z 1%nat (ELit 1) (Z_to_bv 64 1) H966 |];
          constructor; [kwP E M 368%Z 4%nat (ELit (Z.of_nat k)) (Z_to_bv 64 (Z.of_nat k)) Hic |];
          constructor; [kwP E M 524%Z 4%nat (ELit 3) (Z_to_bv 64 3) Hoc |];
          constructor; [kwP E M 352%Z 8%nat (EVar 102) g8 Hg8 |];
          constructor; [kwP E M 360%Z 8%nat (EVar 103) g16 Hg16 |];
          apply know_ok_app; [| exact (know_ok_app SEGS E M KNB _ HKB HKD)];
          unfold KGPS, KGP; cbn [app];
          repeat lazymatch goal with
          | |- ?hd (KWord (SA _ ?o) 1 (EVar ?i) :: KRange _ 2 255 :: _) =>
              let j := eval cbv in (Z.of_nat (i - 104)%nat) in
              let Hb := fresh "Hb" in let Hb1 := fresh "Hb1" in let Hb2 := fresh "Hb2" in
              pose proof (Hgp j ltac:(flia)) as Hb; destruct Hb as [Hb1 Hb2]; unfold LibDefs.cell in Hb2;
              cbn [Z.to_nat Pos.to_nat nth Pos.iter_op Nat.add] in Hb1, Hb2;
              constructor; [kwP E M o 1%nat (EVar i) (Z_to_bv 64 (nth (Z.to_nat j) gps 0%Z)) Hb2 |];
              constructor; [apply krange_intro; cbn [edenot]; ev_simpl E; rewrite u_small by flia; cbn [Z.to_nat Pos.to_nat nth Pos.iter_op Nat.add]; flia |];
              clear Hb1 Hb2
          | |- ?hd [] => constructor
          end
        | clear HKB HKD; unfold KNB in HK; cbn [app] in HK ]
      end end end end.
    (* [comment removed for export] *)
    Ltac callsB :=
      run_fp 100%nat [0x80328%Z; 0x80158%Z] noscr false;
      lazymatch goal with
      | |- runs_to _ (mkst _ (Z_to_bv 64 0x80328) _ _) _ => call_rte_auto 0x8014c%Z; callsB
      | |- _ => idtac
      end.
    (* [comment removed for export] *)
    Ltac gnia := cbn [zprod length Z.of_nat Pos.of_succ_nat Pos.succ Z.pow Z.pow_pos Pos.iter Z.mul Pos.mul];
      first [ (eapply gp_b4; eassumption) | (eapply gp_b3; eassumption) | (eapply gp_b2; eassumption) | (eapply gp_b1; eassumption)   (* [comment removed for export] *)
            | (eapply gp_m3; eassumption) | (eapply gp_m2; eassumption) | (eapply gp_m1; eassumption)
            | (lazymatch goal with |- @eq Z _ _ => ring end)
            | match goal with Ga : (2 <= ?a <= 255)%Z |- (0 <= ?a < _)%Z => clear - Ga; lia end
            | (lazymatch goal with |- (0 <= 3 < _)%Z => clear; lia end)
            | match goal with Ga : (2 <= _ <= 255)%Z, Gb : (2 <= _ <= 255)%Z, Gc : (2 <= _ <= 255)%Z, Gd : (2 <= _ <= 255)%Z |- _ =>
                clear - Ga Gb Gc Gd; nia end
            | match goal with Ga : (2 <= _ <= 255)%Z, Gb : (2 <= _ <= 255)%Z, Gc : (2 <= _ <= 255)%Z |- _ => clear - Ga Gb Gc; nia end
            | match goal with Ga : (2 <= _ <= 255)%Z, Gb : (2 <= _ <= 255)%Z |- _ => clear - Ga Gb; nia end
            | match goal with Ga : (2 <= _ <= 255)%Z |- _ => clear - Ga; nia end
            | (cbn [zprod length Z.of_nat Pos.of_succ_nat Pos.succ Z.pow Z.pow_pos Pos.iter Z.mul Pos.mul] in *; nia) ].
    Ltac finishB GPS H64i :=
      run_fp 100%nat [0x8019c%Z] noscr false;
      lazymatch goal with HA : A2BF ?Mx _ _ ?g8 ?g16, HP : parsed_ok _ ?Mx _ _ _ _, Hin : _ -> _ /\ _ |- _ =>
      pose proof HA as (_ & ?HocF & ?Hg8F & ?Hg16F & _ & _);
      eapply (phaseB2 _ _ _ g8 g16 (3 * zprod GPS)%Z);
        [ base_now H64i | creg (20%bv:reg)
        | lazymatch goal with HR : regs_ok _ _ ?R' |- getr ?R' _ = _ => regv HR (12%bv:reg) end;
          repeat (rewrite mul3_word by gnia); apply (f_equal (Z_to_bv 64)); gnia
        | assumption
        | exact HP
        | exact HocF
        | exact Hg8F
        | exact Hg16F
        | exact (proj1 (Hin ltac:(flia)))
        | exact (proj2 (Hin ltac:(flia)))
        | gnia ]
      end.
    destruct gps as [|g0 [|g1 [|g2 [|g3 [|g4 gps']]]]]; cbn [length] in Hlen, HZP; subst ic;
      [ | | | | | exfalso; flia ].
    - caseB [g8; g16] HA (eq_refl (Z.of_nat 0)) HB Hgw R20.
      run_fp 100%nat [0x80228%Z] noscr false.
      pose proof HA as (_ & HocF & _).
      apply phaseC; [base_now H64i | creg (20%bv:reg) | exact Hn0 | exact HP | exact HocF].
    - pose proof (Hgps g0 ltac:(in_lit)) as G0.
      caseB [g8; g16; Z_to_bv 64 g0] HA (eq_refl (Z.of_nat 1)) HB Hgw R20.
      callsB. finishB [g0] H64i.
    - pose proof (Hgps g0 ltac:(in_lit)) as G0. pose proof (Hgps g1 ltac:(in_lit)) as G1.
      caseB [g8; g16; Z_to_bv 64 g0; Z_to_bv 64 g1] HA (eq_refl (Z.of_nat 2)) HB Hgw R20.
      callsB. finishB [g0; g1] H64i.
    - pose proof (Hgps g0 ltac:(in_lit)) as G0. pose proof (Hgps g1 ltac:(in_lit)) as G1. pose proof (Hgps g2 ltac:(in_lit)) as G2.
      caseB [g8; g16; Z_to_bv 64 g0; Z_to_bv 64 g1; Z_to_bv 64 g2] HA (eq_refl (Z.of_nat 3)) HB Hgw R20.
      callsB. finishB [g0; g1; g2] H64i.
    - pose proof (Hgps g0 ltac:(in_lit)) as G0. pose proof (Hgps g1 ltac:(in_lit)) as G1. pose proof (Hgps g2 ltac:(in_lit)) as G2.
      pose proof (Hgps g3 ltac:(in_lit)) as G3.
      caseB [g8; g16; Z_to_bv 64 g0; Z_to_bv 64 g1; Z_to_bv 64 g2; Z_to_bv 64 g3] HA (eq_refl (Z.of_nat 4)) HB Hgw R20.
      callsB. finishB [g0; g1; g2; g3] H64i.
  Qed.
End Proof.
