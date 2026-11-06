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
From OSSVerify.skcms.iccprofile_info.images Require Import AsanUbsan.
From OSSVerify.Proofs.skcms.iccprofile_info.lib.Info Require Import PropExec CatExec CatSim SeqExec StoreOk SymExec Hoare Frame PropExecFP.
From OSSVerify.Proofs.skcms.iccprofile_info.lib.Info Require Import LibDefs LibFrame LibTagsSpec FuzzContract.
From OSSVerify.Proofs.skcms.iccprofile_info.lib.AsLib Require Import AsSymExec AsSymExecSound AsSymRun AsSymDrive AsSymCall AsFuzzContract AsLibShadow AsLibDefs BoBase BoLibDefs AsRtSpec AsLibTagsSpec AsLibWP1Spec AsLibTagsLib AsLibFPLib AsLibParseLib AsLibFrame AsLibEnv AsLibParseSpec AsLibKit BoLibSpec AsLibPlace.
From OSSVerify.Proofs.skcms.iccprofile_info.lib.AsLib Require Import AsSymDriveLZ.
Import ListNotations.
Open Scope bv_scope.
Import ASX. Import ASXS.
Ltac Zify.zify_post_hook ::= idtac.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Unset Lia Cache. Unset Nia Cache.   (* [comment removed for export] *)

#[local] Abbreviation SEGS := AsanUbsan.M.loaded_segments.

(* [comment removed for export] *)
Ltac lia1f := first [ clia | match goal with H : _ \/ _ |- _ => (destruct H as [H|H]; clia) end ].

(* [comment removed for export] *)
Ltac flia := first [ clia | lia ].
#[local] Abbreviation TP := 0x5da970%Z.
#[local] Abbreviation GF := 0x5da040%Z.
#[local] Abbreviation DEPTH := 3584%Z.

(* [comment removed for export] *)
Ltac in_lit := cbn; repeat (first [left; reflexivity | right]).
Ltac Zify.zify_post_hook ::= Z.div_mod_to_equations.
Ltac Zify.zify_post_hook ::= idtac.

From OSSVerify.Proofs.skcms.iccprofile_info.lib.AsLib Require Import BoLibFuzzADefs.
From OSSVerify.Proofs.skcms.iccprofile_info.lib.AsLib Require BoLibFuzzAHdr.
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
#[local] Abbreviation realign160 := BoLibFuzzAHdr.realign160.
#[local] Abbreviation gfool_apart := BoLibFuzzAHdr.gfool_apart.

Section Proof.
  Variable ceil : Z.
  (* [comment removed for export] *)
  Hypothesis Hparse : parse_contract_bo SEGS as_both ceil.
  Hypothesis Hgetidx : getidx_contract_as SEGS as_both ceil.
  Hypothesis Hrte : rte_contract_as SEGS as_both ceil.
  Hypothesis Hsm5 : stkmalloc5_contract SEGS as_both ceil.
  Hypothesis Hsf5 : stkfree5_contract SEGS as_both ceil.
  Hypothesis Hs00 : setsh00_contract SEGS as_both.
  Hypothesis Hsf8 : setshf8_contract SEGS as_both.

  Hypothesis Hparse0 : parse0_contract ceil.

  (* [comment removed for export] *)
  Variables (FP0 : FPState) (regs : bvmap 5 word) (mem rom : word -> option byte).
  Variables (ret sp data : word) (n : Z) (bs : list byte) (fs : Z) (h0 h5 ctx thr t48 t56 dtls v24 : word).

  (* [comment removed for export] *)
  Hypothesis HALL : FENV ceil regs mem ret sp data n bs fs h0 h5 ctx thr t48 t56 dtls v24.

  (* [comment removed for export] *)
  #[local] Abbreviation pos := (BoLibFuzzAHdr.pos h5).
  #[local] Abbreviation F := (BoLibFuzzAHdr.F fs h5).
  #[local] Abbreviation fa := (BoLibFuzzAHdr.fa fs h5).
  #[local] Abbreviation Uw := (BoLibFuzzAHdr.Uw sp).
  #[local] Abbreviation F_eq := (BoLibFuzzAHdr.F_eq fs h5).
  #[local] Abbreviation fa_eq := (BoLibFuzzAHdr.fa_eq fs h5).
  #[local] Abbreviation pos_eq := (BoLibFuzzAHdr.pos_eq h5).
  #[local] Abbreviation placement := (BoLibFuzzAHdr.placement ceil regs mem ret sp data n bs fs h0 h5 ctx thr t48 t56 dtls v24 HALL).
  #[local] Abbreviation F8k := (BoLibFuzzAHdr.F8k ceil regs mem ret sp data n bs fs h0 h5 ctx thr t48 t56 dtls v24 HALL).
  #[local] Abbreviation nums_zone := (BoLibFuzzAHdr.nums_zone ceil regs mem ret sp data n bs fs h0 h5 ctx thr t48 t56 dtls v24 HALL).
  #[local] Abbreviation BIGF := (BoLibFuzzAHdr.BIGF sp fs).
  #[local] Abbreviation in_bigf := (BoLibFuzzAHdr.in_bigf sp fs).
  #[local] Abbreviation bincl_of := (BoLibFuzzAHdr.bincl_of sp fs).
  #[local] Abbreviation frame_BIGF_app := (BoLibFuzzAHdr.frame_BIGF_app ceil regs mem ret sp data n bs fs h0 h5 ctx thr t48 t56 dtls v24 HALL).
  #[local] Abbreviation in_stack := (BoLibFuzzAHdr.in_stack ceil regs mem ret sp data n bs fs h0 h5 ctx thr t48 t56 dtls v24 HALL).
  #[local] Abbreviation in_gfool := (BoLibFuzzAHdr.in_gfool ceil regs mem ret sp data n bs fs h0 h5 ctx thr t48 t56 dtls v24 HALL).
  #[local] Abbreviation in_hint0 := (BoLibFuzzAHdr.in_hint0 ceil regs mem ret sp data n bs fs h0 h5 ctx thr t48 t56 dtls v24 HALL).
  #[local] Abbreviation in_hint5 := (BoLibFuzzAHdr.in_hint5 ceil regs mem ret sp data n bs fs h0 h5 ctx thr t48 t56 dtls v24 HALL).
  #[local] Abbreviation in_flags0 := (BoLibFuzzAHdr.in_flags0 ceil regs mem ret sp data n bs fs h0 h5 ctx thr t48 t56 dtls v24 HALL).
  #[local] Abbreviation in_flags5 := (BoLibFuzzAHdr.in_flags5 ceil regs mem ret sp data n bs fs h0 h5 ctx thr t48 t56 dtls v24 HALL).
  #[local] Abbreviation in_frames0 := (BoLibFuzzAHdr.in_frames0 ceil regs mem ret sp data n bs fs h0 h5 ctx thr t48 t56 dtls v24 HALL).
  #[local] Abbreviation in_frames5 := (BoLibFuzzAHdr.in_frames5 ceil regs mem ret sp data n bs fs h0 h5 ctx thr t48 t56 dtls v24 HALL).
  #[local] Abbreviation in_shframes0 := (BoLibFuzzAHdr.in_shframes0 ceil regs mem rom ret sp data n bs fs h0 h5 ctx thr t48 t56 dtls v24 HALL).
  #[local] Abbreviation in_shframes5 := (BoLibFuzzAHdr.in_shframes5 ceil regs mem rom ret sp data n bs fs h0 h5 ctx thr t48 t56 dtls v24 HALL).
  #[local] Abbreviation apart_env_bigf := (BoLibFuzzAHdr.apart_env_bigf ceil regs mem rom ret sp data n bs fs h0 h5 ctx thr t48 t56 dtls v24 HALL).
  #[local] Abbreviation apart_heap_bigf := (BoLibFuzzAHdr.apart_heap_bigf ceil regs mem rom ret sp data n bs fs h0 h5 ctx thr t48 t56 dtls v24 HALL).
  #[local] Abbreviation apart_data_bigf := (BoLibFuzzAHdr.apart_data_bigf ceil regs mem rom ret sp data n bs fs h0 h5 ctx thr t48 t56 dtls v24 HALL).
  #[local] Abbreviation apart_stsh_bigf := (BoLibFuzzAHdr.apart_stsh_bigf ceil regs mem rom ret sp data n bs fs h0 h5 ctx thr t48 t56 dtls v24 HALL).
  #[local] Abbreviation apart_hdr_bigf := (BoLibFuzzAHdr.apart_hdr_bigf ceil regs mem rom ret sp data n bs fs h0 h5 ctx thr t48 t56 dtls v24 HALL).
  #[local] Abbreviation as_env_bigf := (BoLibFuzzAHdr.as_env_bigf ceil regs mem rom ret sp data n bs fs h0 h5 ctx thr t48 t56 dtls v24 HALL).
  #[local] Abbreviation fs_hdr_bigf := (BoLibFuzzAHdr.fs_hdr_bigf ceil regs mem rom ret sp data n bs fs h0 h5 ctx thr t48 t56 dtls v24 HALL).
  #[local] Abbreviation fs_writable_bigf := (BoLibFuzzAHdr.fs_writable_bigf ceil regs mem ret sp data n bs fs h0 h5 ctx thr t48 t56 dtls v24 HALL).
  #[local] Abbreviation data_bigf := (BoLibFuzzAHdr.data_bigf ceil regs mem rom ret sp data n bs fs h0 h5 ctx thr t48 t56 dtls v24 HALL).
  #[local] Abbreviation stsh_bigf := (BoLibFuzzAHdr.stsh_bigf ceil regs mem rom ret sp data n bs fs h0 h5 ctx thr t48 t56 dtls v24 HALL).
  #[local] Abbreviation writable_at := (BoLibFuzzAHdr.writable_at mem sp fs).
  #[local] Abbreviation SAVED13 := (BoLibFuzzAHdr.SAVED13 regs sp).
  #[local] Abbreviation flags5_but := (BoLibFuzzAHdr.flags5_but fs h5).
  #[local] Abbreviation MEMB := (BoLibFuzzAHdr.MEMB regs mem sp fs h5).
  #[local] Abbreviation BASE := (BoLibFuzzAHdr.BASE regs mem sp fs h5).
  #[local] Abbreviation SAVED13_frame := (BoLibFuzzAHdr.SAVED13_frame ceil regs mem ret sp data n bs fs h0 h5 ctx thr t48 t56 dtls v24 HALL).
  #[local] Abbreviation MEMB_frame := (BoLibFuzzAHdr.MEMB_frame ceil regs mem ret sp data n bs fs h0 h5 ctx thr t48 t56 dtls v24 HALL).
  #[local] Abbreviation SFe := BoLibFuzzAHdr.SFe.
  #[local] Abbreviation SF8e := BoLibFuzzAHdr.SF8e.
  #[local] Abbreviation SRB := BoLibFuzzAHdr.SRB.
  #[local] Abbreviation KNB := BoLibFuzzAHdr.KNB.
  #[local] Abbreviation KND := (BoLibFuzzAHdr.KND n).
  #[local] Abbreviation packB := (BoLibFuzzAHdr.packB ceil regs mem rom ret sp data n bs fs h0 h5 ctx thr t48 t56 dtls v24 HALL).
  #[local] Abbreviation Q := (BoLibFuzzAHdr.Q regs mem rom ret sp fs).
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
  Ltac sc_lia ::= first [ nlia | clia | dlia ].
  #[local] Opaque BoLibFuzzAHdr.Uw.
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


  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Hypothesis phaseE : forall (FPX : FPState) R M, BASE R M ->
    runs_to SEGS (mkst (FP:=FPX) R (Z_to_bv 64 0x8030c) M rom) Q.
  (* [comment removed for export] *)
  #[local] Abbreviation as_sb_bigf := (BoLibFuzzAHdr.as_sb_bigf ceil regs mem rom ret sp data n bs fs h0 h5 ctx thr t48 t56 dtls v24 HALL).
  #[local] Abbreviation curves_pick := (BoLibFuzzAHdr.curves_pick data n fs h5).
  #[local] Abbreviation MEMB_gf := (BoLibFuzzAHdr.MEMB_gf ceil regs mem ret sp data n bs fs h0 h5 ctx thr t48 t56 dtls v24 HALL).
  #[local] Abbreviation after_rte := (BoLibFuzzAHdr.after_rte ceil regs mem ret sp data n bs fs h0 h5 ctx thr t48 t56 dtls v24 HALL).
  #[local] Abbreviation A2BF := (BoLibFuzzAHdr.A2BF fs h5).
  #[local] Abbreviation A2BF_rte := (BoLibFuzzAHdr.A2BF_rte ceil regs mem ret sp data n bs fs h0 h5 ctx thr t48 t56 dtls v24 HALL).
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
        | unfold rte_pre_as; cbn [al_abi as_both]; rewrite !u_small by flia; pose proof HMB as (_ & ?HM2 & _ & _ & _ & _ & _ & ?HM8 & _);
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
      split; [regv HR (18%bv:reg); reflexivity|];
      split; [regv HR (27%bv:reg); reflexivity|];
      exact HMB
    end end.


  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Hypothesis phaseC : forall (FPX : FPState) R M, BASE R M ->
    getr R 20 = Z_to_bv 64 P -> (0 < n)%Z ->
    parsed_ok SEGS M data n bs P -> cell32 SEGS M (P + 460) 3 ->
    runs_to SEGS (mkst (FP:=FPX) R (Z_to_bv 64 0x80298) M rom) Q.

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
    runs_to SEGS (mkst (FP:=FPX) R (Z_to_bv 64 0x801f4) M rom) Q.

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

  Hypothesis phaseB : forall (FPX : FPState) R M, BASE R M ->
    getr R 20 = Z_to_bv 64 P ->
    parsed_ok SEGS M data n bs P ->
    runs_to SEGS (mkst (FP:=FPX) R (Z_to_bv 64 0x80160) M rom) Q.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Ltac gfstep :=
    let Hfrg := fresh "Hfrg" in let HG := fresh "HG" in
    log_frameF [(SA (ELit 0) GF, 4%Z)] Hfrg; change (0 + 0x5da040)%Z with 0x5da040%Z in Hfrg;
    lazymatch goal with HK : know_ok _ _ _ _ |- _ =>
      kcell_auto HK (ELit 0) 0x5da040%Z 4%nat HG; rewrite ?u_small in HG by flia; change (0 + 0x5da040)%Z with 0x5da040%Z in HG end;
    lazymatch goal with HMB : MEMB ?Ma, HP : parsed_ok _ ?Ma _ _ _ _ |- runs_to _ (@mkst _ _ _ ?Mn _) _ =>
      let HMB' := fresh "HMB" in let HP' := fresh "HP" in
      pose proof (MEMB_gf _ Mn HMB Hfrg ltac:(eexists; exact HG)) as HMB';
      assert (HP' : parsed_ok SEGS Mn data n bs P) by (eapply parsed_ok_frame; [exact Hfrg | exact HP | flia | flia | solve_apart | solve_apart | solve_apart]);
      clear HMB HP Hfrg HG; rename HMB' into HMB; rename HP' into HP end.

  Lemma phaseA2 : forall (FPX : FPState) R M, BASE R M ->
    getr R 20 = Z_to_bv 64 P ->
    parsed_ok SEGS M data n bs P ->
    runs_to SEGS (mkst (FP:=FPX) R (Z_to_bv 64 0x80124) M rom) Q.
  Proof.
    intros FPX R M HB R20 HP. pose proof HB as (R2 & R9 & R8 & R3 & R4 & R19 & R21 & R25 & R18 & R27 & HMB).
    pose proof HMB as (_ & HM2 & _ & _ & _ & _ & _ & _ & [gw Hgw]).
    need_nums. need_regs. pose proof placement as PL.
    pose proof PL as (P0 & P1 & P2 & P3 & P4 & P5 & P6 & P7 & P8 & P9 & P10 & P11 & P12 & P13 & P14 & _). clear PL.
    pose proof (u64_range sp) as Hspr. pose proof (u64_range data) as Hdr.
    pose proof HP as (psz & tc & htrc & hasA2B & _ & _ & _ & Htags & _ & [_ H964] & Hht & _).
    assert (Hn0 : (0 < n)%Z) by (destruct Htags as (Ht0 & Ht & _); flia).
    destruct (data_bigf M HM2 Hn0) as ((HD1 & HD2 & HD3 & HD4) & Hdar). pose proof HD1 as (D1 & D2 & D3 & D4 & D5).
    unfold heapish in HD2. app_facts. clear HM2.
    unfold LibDefs.cell in H964.
    destruct (packB R (fp_regs (FPState:=FPX)) M gw [] HB Hgw) as (HR & HF & HKB & HKD & H64).
    pose proof (H64 : id _) as H64i. clear H64. rewrite (KND_pos Hn0) in HKD.
    apply (regs_ok_pin _ _ R 20 (EAlu ALU_ADD (EVar 97) (ELit 64))) in HR;
      [| cbn [edenot]; ev_simpl_goal; rewrite alu_add_lit, u_small by flia; rewrite R20; apply (f_equal (Z_to_bv 64)); flia].
    lazymatch type of HR with regs_ok ?E _ _ =>
      assert (HK : know_ok SEGS E M (KWord (SA (EVar 97) 1028) 1 (ELit htrc) :: KNB ++ [KRange (EAlu ALU_ADD (EVar 74) (EVar 100)) 0 (2 ^ 47 - 2048); KRange (EVar 74) 1 (2 ^ 47 - 2048); KShad (EVar 74) (EVar 100) SB; KBlobD (SA (EVar 74) 0) (EVar 100) 0]));
      [ constructor; [| exact (know_ok_app SEGS E M KNB _ HKB HKD)];
        eapply (kword_intro SEGS E M (EVar 97) (Z_to_bv 64 F) 1028 1 (ELit htrc) (Z_to_bv 64 htrc));
          [cbn [edenot]; ev_simpl E; reflexivity | reflexivity | flia | flia | rewrite u_small by flia; flia | rewrite u_small by flia; cbn; flia |
           rewrite u_small by flia; replace (F + 1028)%Z with (F + 64 + 964)%Z by flia; exact H964]
      | clear HKB HKD; unfold KNB in HK; cbn [app] in HK ] end.
    clear Hgw H964.
    destruct Hht as [-> | ->].
    { (* [comment removed for export] *)
      run_fp 30%nat [0x80160%Z] noscr false. apply phaseB; [base_now H64i | creg (20%bv:reg) | exact HP]. }
    run_fp 30%nat [0x803c4%Z] noscr false.
    call_rte 0x8014c%Z 24%Z.
    run_fp 30%nat [0x803c4%Z; 0x80160%Z] noscr true. gfstep.
    call_rte 0x8014c%Z 56%Z.
    run_fp 30%nat [0x803c4%Z; 0x80160%Z] noscr true. gfstep.
    call_rte 0x8014c%Z 88%Z.
    run_fp 30%nat [0x803c4%Z; 0x80160%Z] noscr true. gfstep.
    apply phaseB; [base_now H64i | creg (20%bv:reg) | exact HP].
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Ltac Zify.zify_post_hook ::= Z.div_mod_to_equations.
  Lemma addw_small : forall (x : word) (k sv : Z),
    bv_unsigned x = sv -> (0 <= sv < 2^32)%Z -> (0 <= sv + k < 2^31)%Z -> (-2^31 <= k <= 0)%Z ->
    sext 64 (alu32 ALU_ADD (low32 x) (low32 (Z_to_bv 64 k))) = Z_to_bv 64 (sv + k).
  Proof.
    intros x k sv Hx Hs Hsk Hk. apply bv_eq. rewrite sext32_unsigned, Z_to_bv_unsigned.
    change (alu32 ALU_ADD (low32 x) (low32 (Z_to_bv 64 k))) with (low32 x + low32 (Z_to_bv 64 k))%bv.
    rewrite bv_add_unsigned, !low32_unsigned, !Z_to_bv_unsigned, Hx.
    unfold bv_swrap. rewrite !bv_wrap32_mod, !bv_wrap64_mod.
    change (bv_half_modulus 32) with (2^31)%Z. nia.
  Qed.
  Ltac Zify.zify_post_hook ::= idtac.

  (* [comment removed for export] *)
  Lemma after_getidx : forall M M', MEMB M -> parsed_ok SEGS M data n bs P ->
    frame_mod M M' [(Z_to_bv 64 (bv_unsigned Uw - 16), 16%Z); (Z_to_bv 64 T, 24%Z)] ->
    MEMB M' /\ parsed_ok SEGS M' data n bs P.
  Proof.
    intros M M' HM HP Hf. need_nums. pose proof placement as PL. hide PL. pose proof (u64_range sp).
    pose proof (unhide PL) as (P1&P2&P3&_&_&_&_&_&P9&_&_&P12&_).
    split.
    - eapply MEMB_frame; [exact HM | exact Hf | apply bincl_of; constructor; [cbn [fst snd]; apply in_stack; flia|constructor; [cbn [fst snd]; apply in_frames5; flia|constructor]] |..];
        unfold SB; try solve_apart.
      all: clear PL. Ltac Zify.zify_post_hook ::= Z.div_mod_to_equations. all: flia. Ltac Zify.zify_post_hook ::= idtac.
    - eapply parsed_ok_frame; [exact Hf | exact HP | flia | flia | solve_apart | solve_apart | solve_apart].
  Qed.

  (* [comment removed for export] *)
  Definition poke_regions (rs : list (word * Z)) : Prop :=
    Forall (fun r => (bv_unsigned (fst r) = SF + 4 /\ snd r = 1) \/ (SF + 146 <= bv_unsigned (fst r) /\ bv_unsigned (fst r) + snd r <= SF + 149 /\ 0 <= snd r))%Z rs.

  Lemma poke_apart : forall rs, poke_regions rs ->
    (forall lo k, (lo + k <= SF + 4 \/ (SF + 5 <= lo /\ lo + k <= SF + 146) \/ SF + 149 <= lo)%Z -> apart lo k rs) /\ regions_incl rs BIGF.
  Proof.
    intros rs Hrs. need_nums. pose proof placement as (P1&P2&P3&_&_&P5&_). split.
    - intros lo k Hlo. unfold apart. eapply Forall_impl; [|exact Hrs]. intros [b m] Hb. cbn [fst snd] in *. flia.
    - apply bincl_of. eapply Forall_impl; [|exact Hrs]. intros [b m] Hb. cbn [fst snd] in *.
      rewrite <- (Z_to_bv_bv_unsigned 64 b). apply in_shframes5; unfold SB in *; flia.
  Qed.

  Lemma MEMB_pokes : forall M M' rs, MEMB M -> frame_mod M M' rs -> poke_regions rs -> MEMB M'.
  Proof.
    intros M M' rs HM Hf Hrs. need_nums. pose proof placement as PL. hide PL. pose proof (u64_range sp).
    pose proof (unhide PL) as (P1&P2&P3&_&_&P5&_&_&P9&_&_&P12&_).
    destruct (poke_apart rs Hrs) as [Hap Hin]. clear Hrs. unfold SB in Hap.
    Ltac Zify.zify_post_hook ::= Z.div_mod_to_equations.
    pose proof (app_sh_lit _ _ Hfslo) as Fsh.
    eapply MEMB_frame; [exact HM | exact Hf | exact Hin |..]; apply Hap; clear PL; unfold SB; dlia.
    Ltac Zify.zify_post_hook ::= idtac.
  Qed.

  Lemma parsed_pokes : forall M M' rs, parsed_ok SEGS M data n bs P -> frame_mod M M' rs -> poke_regions rs -> parsed_ok SEGS M' data n bs P.
  Proof.
    intros M M' rs HP Hf Hrs. need_nums. pose proof placement as PL. hide PL. pose proof (u64_range sp).
    pose proof (unhide PL) as (P1&P2&P3&_&_&P5&_&_&P9&_&_&P12&_).
    destruct (poke_apart rs Hrs) as [Hap Hin]. clear Hrs. unfold SB in Hap.
    Ltac Zify.zify_post_hook ::= Z.div_mod_to_equations.
    pose proof (app_sh_lit _ _ Hfslo) as Fsh.
    eapply parsed_ok_frame; [exact Hf | exact HP | flia | flia | apply Hap; clear PL; unfold SB; dlia..].
    Ltac Zify.zify_post_hook ::= idtac.
  Qed.

  (* [comment removed for export] *)
  Ltac pokes_ok := unfold poke_regions; repeat (apply Forall_cons; [cbn [fst snd]; rewrite u_small by (unfold SB in *; flia); unfold SB; flia|]); apply Forall_nil.

  Ltac call_getidx RET IDX H0 Htc Htags :=
    lazymatch goal with |- runs_to _ (@mkst ?I ?R' _ ?M' _) _ =>
    lazymatch goal with HR : regs_ok _ _ R', HMB : MEMB M', HP : parsed_ok _ M' _ _ _ _, Hn0 : (0 < n)%Z, HshT : shz M' T 3 |- _ =>
    lazymatch type of Htags with tags_ok _ _ ?tcv ?pszv =>
      pose proof HMB as (_ & ?HM2 & _ & _ & _ & _ & _ & ?HM8 & _);
      eapply rt_call;
      [ eapply (Hgetidx data n bs (Z_to_bv 64 P) tcv pszv IDX (Z_to_bv 64 T) I R' M' rom (Z_to_bv 64 RET));
        [ regv HR (1%bv:reg); reflexivity
        | apply ret_ok_even; rewrite u_small by flia; reflexivity
        | unfold getidx_pre_as; cbv zeta; cbn [al_abi as_both]; rewrite !u_small by flia;
          split; [regv HR (10%bv:reg); rewrite_getr; rewrite ?alu_add_lit; rewrite ?u_small by flia; apply (f_equal (Z_to_bv 64)); flia|];
          split; [regv HR (11%bv:reg); first [reflexivity | rewrite (addw_small _ (-1) (IDX + 1)) by (rewrite ?u_small by flia; flia); apply (f_equal (Z_to_bv 64)); flia]|];
          split; [regv HR (12%bv:reg); rewrite_getr; rewrite ?alu_add_lit; rewrite ?u_small by flia; apply (f_equal (Z_to_bv 64)); flia|];
          split; [pose proof Htags as (? & ? & _); flia|];
          split; [exact (proj1 (data_bigf M' HM2 Hn0))|];
          split; [unfold cell64; exact H0|]; split; [split; [pose proof Htags as (? & ? & _); flia | exact Htc]|]; split; [exact Htags|];
          split; [apply F8k; reflexivity|];
          split; [unfold heapish; plc|];
          split; [eapply (shz_sub M' _ _ _ _ HM8); [apply F8k; reflexivity | flia | flia | flia]|];
          split; [apply F8k; reflexivity|];
          split; [unfold heapish; plc|];
          split; [eapply (writable_at M' _ _ T 24 HM2 (Hwfr5 HALL)); unfold FS_FRAMES5, FS_FRAMES_LEN; flia|];
          split; [exact HshT|];
          split; [pose proof (proj2 (data_bigf M' HM2 Hn0)) as Hdar'; unfold FS_SIZE in Hdar'; flia|];
          split; [flia|];
          split; [exact (as_sb_bigf M' HM2)|];
          exists Uw; split; [regv HR (2%bv:reg); reflexivity|];
          unfold as_frame, stackish; split; [flia|]; split; [apply (mod_down (bv_unsigned Uw) 16 2); [flia|flia|assumption]|];
          eapply (writable_at M' _ _ (bv_unsigned Uw - 16) 16 HM2 (Hstw HALL)); flia ]
      | cbv beta; clear HM2 HM8;
        let FPI' := fresh "FPI" in let regs' := fresh "R" in let mem' := fresh "MG" in
        let Hkeep := fresh "Hkeep" in let Hfkeep := fresh "Hfkeep" in let Hpost := fresh "Hpost" in let Hfr := fresh "Hfr" in let HX := fresh "HX2" in
        intros FPI' regs' mem' (Hkeep & Hfkeep & Hpost);
        unfold getidx_post_as in Hpost; cbv zeta in Hpost; destruct Hpost as (Hfr & _);
        assert (HX : getr R' 2 = Uw) by (regv HR (2%bv:reg); reflexivity); rewrite HX in Hfr; clear HX;
        unfold regs_kept in Hkeep; unfold fregs_kept in Hfkeep; after_call Hkeep Hfkeep FPI'; clear Hkeep Hfkeep;
        lazymatch goal with HK : know_ok _ _ _ _ |- _ => kframe HK Hfr [(SA (EVar 96) (-16), 16%Z); (SA (EVar 97) 1168, 24%Z)] end;
        let HMB' := fresh "HMB" in let HP' := fresh "HP" in let HshT' := fresh "HshT" in let H0' := fresh "HP0" in let Htc' := fresh "HP20" in
        destruct (after_getidx M' mem' HMB HP Hfr) as [HMB' HP'];
        assert (HshT' : shz mem' T 3) by (eapply shz_frame; [exact Hfr | exact HshT | flia | flia | unfold SB in *; solve_apart]);
        assert (H0' : LibDefs.cell SEGS mem' (F + 64) 8 data) by (eapply cell_frame; [exact Hfr | exact H0 | flia | cbn; flia | solve_apart]);
        assert (Htc' : LibDefs.cell SEGS mem' (F + 64 + 20) 4 (Z_to_bv 64 tcv)) by (eapply cell_frame; [exact Hfr | exact Htc | flia | cbn; flia | solve_apart]);
        clear Hfr HMB HP HshT H0 Htc; rename HMB' into HMB; rename HP' into HP; rename HshT' into HshT; rename H0' into H0; rename Htc' into Htc ]
    end end end.

  Lemma phaseA1 : forall (FPX : FPState) R M (r : Z), BASE R M ->
    getr R 20 = Z_to_bv 64 P -> getr R 10 = Z_to_bv 64 r -> (r = 0 \/ r = 1)%Z ->
    (r = 1%Z -> parsed_ok SEGS M data n bs P) ->
    runs_to SEGS (mkst (FP:=FPX) R (Z_to_bv 64 0x800d0) M rom) Q.
  Proof.
    intros FPX R M r HB R20 R10 Hr HPr. pose proof HB as (R2 & R9 & R8 & R3 & R4 & R19 & R21 & R25 & R18 & R27 & HMB).
    pose proof HMB as (_ & HM2 & _ & _ & _ & _ & _ & _ & [gw Hgw]).
    need_nums. need_regs. pose proof placement as PL.
    pose proof PL as (P0 & P1 & P2 & P3 & P4 & P5 & P6 & P7 & P8 & P9 & P10 & P11 & P12 & P13 & P14 & _). clear PL.
    pose proof (u64_range sp) as Hspr. pose proof (u64_range data) as Hdr.
    destruct Hr as [Hr | Hr]; subst r.
    { (* [comment removed for export] *)
      destruct (packB R (fp_regs (FPState:=FPX)) M gw [] HB Hgw) as (HR & HF & HK & _ & H64).
      pose proof (H64 : id _) as H64i. clear H64. unfold KNB in HK.
      apply (regs_ok_pin _ _ R 10 (ELit 0)) in HR; [| exact R10].
      run_fp 30%nat [0x8030c%Z] noscr true.
      log_frameF [(SA (EAlu ALU_SRL (EVar 97) (ELit 3)) (SB + 4), 1%Z)] Hfr4.
      lazymatch goal with |- runs_to _ (@mkst _ _ _ ?Mn _) _ =>
        assert (HMBn : MEMB Mn); [| clear HMB; rename HMBn into HMB] end.
      { eapply MEMB_pokes; [exact HMB | exact Hfr4 | pokes_ok]. }
      apply phaseE. base_now H64i. }
    specialize (HPr eq_refl). pose proof HPr as HP.
    destruct HPr as (psz & tc & htrc & hasA2B & H0 & H8 & [Htc32 Htc] & Htags & _).
    assert (Hn0 : (0 < n)%Z) by (destruct Htags as (Ht0 & Ht & _); flia).
    destruct (data_bigf M HM2 Hn0) as ((HD1 & HD2 & HD3 & HD4) & Hdar). pose proof HD1 as (D1 & D2 & D3 & D4 & D5).
    unfold heapish in HD2. app_facts. clear HM2.
    unfold LibDefs.cell in Htc.
    pose proof Htags as (Htc0 & Hpsz & _).
    destruct (Z.eq_dec tc 0) as [Htz | Htnz].
    { (* [comment removed for export] *)
      subst tc.
      destruct (packB R (fp_regs (FPState:=FPX)) M gw [] HB Hgw) as (HR & HF & HKB & _ & H64).
      pose proof (H64 : id _) as H64i. clear H64.
      apply (regs_ok_pin _ _ R 10 (ELit 1)) in HR; [| exact R10].
      apply (regs_ok_pin _ _ R 20 (EAlu ALU_ADD (EVar 97) (ELit 64))) in HR;
        [| cbn [edenot]; ev_simpl_goal; rewrite alu_add_lit, u_small by flia; rewrite R20; apply (f_equal (Z_to_bv 64)); flia].
      lazymatch type of HR with regs_ok ?E _ _ =>
        assert (HK : know_ok SEGS E M (KWord (SA (EVar 97) 84) 4 (ELit 0) :: KNB));
        [ constructor; [| exact HKB];
          eapply (kword_intro SEGS E M (EVar 97) (Z_to_bv 64 F) 84 4 (ELit 0) (Z_to_bv 64 0));
            [cbn [edenot]; ev_simpl E; reflexivity | reflexivity | flia | flia | rewrite u_small by flia; flia | rewrite u_small by flia; cbn; flia |
             rewrite u_small by flia; replace (F + 84)%Z with (F + 64 + 20)%Z by flia; exact Htc]
        | clear HKB; unfold KNB in HK ] end.
      run_fp 30%nat [0x80124%Z] noscr true.
      log_frameF [(SA (EAlu ALU_SRL (EVar 97) (ELit 3)) (SB + 4), 1%Z)] Hfr4.
      lazymatch goal with |- runs_to _ (@mkst _ _ _ ?Mn _) _ =>
        pose proof (MEMB_pokes M Mn _ HMB Hfr4 ltac:(pokes_ok)) as HMBn;
        pose proof (parsed_pokes M Mn _ HP Hfr4 ltac:(pokes_ok)) as HPn;
        clear HMB HP; rename HMBn into HMB; rename HPn into HP end.
      apply phaseA2; [base_now H64i | creg (20%bv:reg) | exact HP]. }
    (* [comment removed for export] *)
    destruct (packB R (fp_regs (FPState:=FPX)) M gw [Z_to_bv 64 tc] HB Hgw) as (HR & HF & HKB & _ & H64).
    pose proof (H64 : id _) as H64i. clear H64.
    apply (regs_ok_pin _ _ R 10 (ELit 1)) in HR; [| exact R10].
    apply (regs_ok_pin _ _ R 20 (EAlu ALU_ADD (EVar 97) (ELit 64))) in HR;
      [| cbn [edenot]; ev_simpl_goal; rewrite alu_add_lit, u_small by flia; rewrite R20; apply (f_equal (Z_to_bv 64)); flia].
    lazymatch type of HR with regs_ok ?E _ _ =>
      assert (HK : know_ok SEGS E M (KWord (SA (EVar 97) 84) 4 (EVar 102) :: KRange (EVar 102) 1 5592405 :: KNB));
      [ constructor; [| constructor; [| exact HKB]];
        [ eapply (kword_intro SEGS E M (EVar 97) (Z_to_bv 64 F) 84 4 (EVar 102) (Z_to_bv 64 tc));
            [cbn [edenot]; ev_simpl E; reflexivity | cbn [edenot]; ev_simpl E; reflexivity | flia | flia | rewrite u_small by flia; flia | rewrite u_small by flia; cbn; flia |
             rewrite u_small by flia; replace (F + 84)%Z with (F + 64 + 20)%Z by flia; exact Htc]
        | apply krange_intro; cbn [edenot]; ev_simpl E; rewrite u_small by flia; flia ]
      | clear HKB; unfold KNB in HK ] end.
    clear Hgw H8. unfold cell64 in H0.
    Ltac Zify.zify_post_hook ::= Z.div_mod_to_equations.
    assert (HT8 : ((F + 1168) / 8 = F / 8 + 146)%Z) by (clear -P4; flia).
    Ltac Zify.zify_post_hook ::= idtac.
    run_fp 40%nat [0x818d8%Z] noscr true.
    (* [comment removed for export] *)
    lazymatch goal with EQM : ?Mn = mem_denot ?E2 ?Mo ?log, HLF : log_flat _ _ |- _ =>
      assert (HshT : shz Mn T 3);
      [ split; [apply F8k; reflexivity|]; intros j Hj; rewrite EQM;
        pose proof (mem_denot_lz_cover E2 Mo log (EAlu ALU_SRL (EVar 97) (ELit 3)) (SB + 146) 3 HLF ltac:(vm_compute; reflexivity)) as HZ;
        rewrite edenot_srl3 in HZ; cbn [edenot] in HZ; ev_simpl_in E2 HZ; rewrite u_small in HZ by flia;
        replace (SB + (F + 1168) / 8 + j)%Z with (F / 8 + (SB + 146 + j))%Z by flia;
        apply HZ; unfold SB; cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; flia | ] end.
    log_frameF [(SA (EAlu ALU_SRL (EVar 97) (ELit 3)) (SB + 4), 1%Z); (SA (EAlu ALU_SRL (EVar 97) (ELit 3)) (SB + 146), 1%Z);
                (SA (EAlu ALU_SRL (EVar 97) (ELit 3)) (SB + 147), 1%Z); (SA (EAlu ALU_SRL (EVar 97) (ELit 3)) (SB + 148), 1%Z)] Hfrp.
    lazymatch goal with |- runs_to _ (@mkst _ _ _ ?Mn _) _ =>
      pose proof (MEMB_pokes M Mn _ HMB Hfrp ltac:(pokes_ok)) as HMBn;
      pose proof (parsed_pokes M Mn _ HP Hfrp ltac:(pokes_ok)) as HPn;
      assert (H0n : LibDefs.cell SEGS Mn (F + 64) 8 data) by (eapply cell_frame; [exact Hfrp | exact H0 | flia | cbn; flia | unfold SB in *; solve_apart]);
      assert (Htcn : LibDefs.cell SEGS Mn (F + 64 + 20) 4 (Z_to_bv 64 tc)) by (eapply cell_frame; [exact Hfrp | exact Htc | flia | cbn; flia | unfold SB in *; solve_apart]);
      clear HMB HP Hfrp H0 Htc; rename HMBn into HMB; rename HPn into HP; rename H0n into H0; rename Htcn into Htc end.
    call_getidx 0x80100%Z 0%Z H0 Htc Htags.
    run_fp 30%nat [0x818d8%Z] noscr false.
    call_getidx 0x80114%Z (tc - 1)%Z H0 Htc Htags.
    run_fp 30%nat [0x80124%Z] noscr true.
    log_frameF [(SA (EAlu ALU_SRL (EVar 97) (ELit 3)) (SB + 146), 1%Z);
                (SA (EAlu ALU_SRL (EVar 97) (ELit 3)) (SB + 147), 1%Z); (SA (EAlu ALU_SRL (EVar 97) (ELit 3)) (SB + 148), 1%Z)] Hfrq.
    lazymatch goal with |- runs_to _ (@mkst _ _ _ ?Mn _) _ =>
      lazymatch type of Hfrq with frame_mod ?Mo _ _ =>
      pose proof (MEMB_pokes Mo Mn _ HMB Hfrq ltac:(pokes_ok)) as HMBn;
      pose proof (parsed_pokes Mo Mn _ HP Hfrq ltac:(pokes_ok)) as HPn;
      clear HMB HP Hfrq; rename HMBn into HMB; rename HPn into HP end end.
    apply phaseA2; [base_now H64i | creg (20%bv:reg) | exact HP].
  Qed.
End Proof.
