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

  Hypothesis phaseA2 : forall (FPX : FPState) R M, BASE R M ->
    getr R 20 = Z_to_bv 64 P ->
    parsed_ok SEGS M data n bs P ->
    runs_to SEGS (mkst (FP:=FPX) R (Z_to_bv 64 0x80124) M rom) Q.

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

  Hypothesis phaseA1 : forall (FPX : FPState) R M (r : Z), BASE R M ->
    getr R 20 = Z_to_bv 64 P -> getr R 10 = Z_to_bv 64 r -> (r = 0 \/ r = 1)%Z ->
    (r = 1%Z -> parsed_ok SEGS M data n bs P) ->
    runs_to SEGS (mkst (FP:=FPX) R (Z_to_bv 64 0x800d0) M rom) Q.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Definition EINV (M : word -> option byte) : Prop :=
    SAVED13 M /\ frame_mod mem M BIGF /\ acellw SEGS M (fs + 0) h0 /\ fs_flags0_but fs [] M /\ flags5_but M /\
    (exists gw, LibDefs.cell SEGS M GF 4 gw).

  Lemma EINV_frame : forall M M' rs, EINV M -> frame_mod M M' rs -> regions_incl rs BIGF ->
    apart (s - 104) 104 rs -> apart (fs + 0) 8 rs -> apart (fs + 0x1000) 0x4000 rs ->
    apart (fs + 0x8c00) pos rs -> apart (fa + 1) (0x200 - pos - 1) rs -> apart GF 4 rs -> EINV M'.
  Proof.
    intros M M' rs (E1 & E2 & E3 & E4 & E5 & E6) Hf Hin A1 A2 A3 A4 A5 A6. need_nums. pose proof placement as (P0&P1&P2&_). pose proof (u64_range sp).
    split; [eapply SAVED13_frame; [exact E1 | exact Hf | exact A1]|].
    split; [eapply frame_BIGF_app; [exact E2 | exact Hf | exact Hin]|].
    split; [eapply acellw_frame; [exact Hf | exact E3 | flia | flia | exact A2]|].
    split. { intros i Hi Hni. unfold FS_FLAGS0, FS_FLAGS0_LEN in *. rewrite (byte_frame M M' rs (fs + 4096 + i) Hf ltac:(flia)); [apply E4; assumption|].
             eapply apart_sub; [exact A3 | flia | flia | flia]. }
    split. { intros i Hi Hni. rewrite (byte_frame M M' rs (fs + 0x8c00 + i) Hf ltac:(flia)); [apply E5; assumption|].
             destruct (Z_lt_le_dec i pos); [eapply apart_sub; [exact A4 | flia | flia | flia] | eapply apart_sub; [exact A5 | flia | flia | flia]]. }
    destruct E6 as [gw Hgw]. exists gw. eapply cell_frame; [exact Hf | exact Hgw | flia | cbn; flia | exact A6].
  Qed.

  (* [comment removed for export] *)
  Lemma after_parse : forall M M' h',
    SAVED13 M -> frame_mod mem M BIGF -> cell64 SEGS M (bv_unsigned Uw + 24) (Z_to_bv 64 SB) -> acell SEGS M (F + 2040) 8 fa ->
    flags5_but M -> shz M P 122 -> (exists gw, LibDefs.cell SEGS M GF 4 gw) ->
    frame_mod M M' ([(Z_to_bv 64 (bv_unsigned Uw - PARSE_DB), PARSE_DB); (Z_to_bv 64 (F + 64), 976%Z)] ++ fs_mod0 fs) ->
    fs_flags0_but fs [] M' -> acellw SEGS M' (fs + FS_HINT0) h' -> MEMB M'.
  Proof.
    intros M M' h' E1 E2 E3 E4 E5 E6 [gw Hgw] Hf Hfl Hh. need_nums. pose proof placement as PL. pose proof (u64_range sp).
    pose proof PL as (P0 & P1 & P2 & P3 & P4 & P5 & P6 & P7 & P8 & P9 & P10 & P11 & P12 & P13 & P14 & _). clear PL.
    unfold fs_mod0, FS_HINT0, FS_FLAGS0, FS_FLAGS0_LEN, FS_FRAMES0, FS_FRAMES_LEN, FS_SHFRAMES_LEN, AS_SB, PARSE_DB in Hf. cbn [app] in Hf.
    Ltac Zify.zify_post_hook ::= Z.div_mod_to_equations.
    assert (HF64 : ((F + 64) / 8 = F / 8 + 8)%Z) by (clear -P4; flia).
    Ltac Zify.zify_post_hook ::= idtac.
    split; [eapply SAVED13_frame; [exact E1 | exact Hf | unfold SB; solve_apart]|].
    split. { eapply frame_BIGF_app; [exact E2 | exact Hf |]. apply bincl_of. repeat (apply Forall_cons); [..|apply Forall_nil]; cbn [fst snd];
             [apply in_stack; flia | apply in_frames5; flia | apply in_hint0 | apply in_flags0; flia | apply in_frames0; flia | apply in_shframes0; unfold SB; flia]. }
    split; [eapply cell64_frame; [exact Hf | exact E3 | flia | flia | unfold SB; solve_apart]|].
    split; [eapply acell_frame; [exact Hf | exact E4 | flia | cbn; flia | unfold SB; solve_apart]|].
    split; [exact Hfl|].
    split; [exists h'; exact Hh|].
    split. { intros i Hi Hni. rewrite (byte_frame M M' _ (fs + 0x8c00 + i) Hf ltac:(flia)); [apply E5; assumption|]. unfold SB; solve_apart. }
    split; [eapply shz_frame; [exact Hf | exact E6 | flia | flia | rewrite HF64; unfold SB; solve_apart]|].
    exists gw. eapply cell_frame; [exact Hf | exact Hgw | flia | cbn; flia | unfold SB; solve_apart].
  Qed.

  Lemma parsed_ok_len0 : forall M d bs' p, parsed_ok SEGS M d 0 bs' p -> False.
  Proof. intros M d bs' p (psz & tc & _ & _ & _ & _ & _ & Ht & _). destruct Ht as (Ht0 & Ht1 & _). flia. Qed.

  Lemma entry_run : runs_to SEGS (mkst (FP:=FP0) regs (Z_to_bv 64 0x7ff14) mem rom) Q.
  Proof.
    need_nums. need_regs. need_wr. need_fs. pose proof placement as PL.
    pose proof PL as (P0 & P1 & P2 & P3 & P4 & P5 & P6 & P7 & P8 & P9 & P10 & P11 & P12 & P13 & P14 & _). clear PL.
    unfold FS_FRAMES5, FS_FRAMES_LEN, FS_SHFRAMES_LEN, FS_FLAGS5, FS_FLAGS5_LEN, FS_FLAGS0, FS_FLAGS0_LEN, FS_HINT0, FS_HINT5, AS_SB in Hwfr5, Hwsf5, Hwfl5, Hwfl0, Hwh0, Hwh5, Hstw, Hh0, Hh5, Hfl0, Hfl5.
    pose proof (u64_range sp) as Hspr. pose proof (u64_range data) as Hdr.
    assert (HB0 : frame_mod mem mem BIGF) by apply frame_mod_refl.
    pose proof (both_cells64 SEGS mem (proj1 (as_env_bigf mem HB0))) as CC.
    destruct CC as (E1 & E2 & E3 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & E22 & _).
    unfold acell in E1, E2, E3, E22.
    set (E := Env (vals_ev (junk_vals regs ++ fjunk_vals (fp_regs (FPState:=FP0)) ++ [Uw; Z_to_bv 64 F; Z_to_bv 64 fa; Z_to_bv 64 fs; Z_to_bv 64 n])) (blobs_ev [bs])).
    assert (HR : regs_ok E (sr_vars 0) regs) by exact (regs_ok_vars [] regs _ (blobs_ev [bs])).
    assert (HF : fregs_ok E (sfr_vars 32) fp_regs) by exact (fregs_ok_vars (junk_vals regs) fp_regs _ (blobs_ev [bs])).
    Ltac klit E0 H := eapply (kword_intro SEGS E0 mem (ELit 0) (Z_to_bv 64 0));
      [reflexivity | cbn [edenot]; ev_simpl E0; reflexivity | flia | flia | rewrite u_lit0; flia | rewrite u_lit0; cbn; flia | rewrite u_lit0, Z.add_0_l; exact H].
    assert (HK : know_ok SEGS E mem
      [KWord (SA (ELit 0) 0x9f920) 8 (ELit 0xa79b8); KWord (SA (ELit 0) 0xa79b8) 8 (ELit SB);
       KWord (SA (ELit 0) 0x9f978) 8 (ELit 0xa79c0); KWord (SA (ELit 0) 0xa79c0) 4 (ELit 1);
       KAlign (EVar 2) 16; KRange (EVar 2) (AS_STKLO + 3584) (2 ^ 47 - 1); KWr (SA (EVar 2) (-3584)) 3584;
       KAlign (EVar 64) 32; KRange (EVar 64) (AS_STKLO + 3408) (2 ^ 47 - 160); KWr (SA (EVar 64) (-2928)) 2984;
       KDisj (SA (EVar 64) (-2928)) 2984 (SA (EVar 2) (-104)) 104;
       KRange (EVar 65) 1 (2 ^ 47 - 2048); KAlign (EVar 65) 2048;
       KRange (EVar 67) 1 (2 ^ 47 - 0xb09000); KRange (EVar 68) 0 (2 ^ 26);
       KDisj (SA (EVar 65) 0) 2048 ZSH ZSHL; KDisj (SA (EVar 65) 0) 2048 ZIMG ZIMGL;
       KDisj (SA (EVar 65) 0) 2048 (SA (EVar 64) (-2896)) 2952; KDisj (SA (EVar 65) 0) 2048 (SA (EVar 2) (-3584)) 3584]).
    { unfold know_ok. repeat (apply Forall_cons); [..|apply Forall_nil].
      - klit E E1. - klit E E2. - klit E E3. - klit E E22.
      - apply kalign_intro; [flia|]. cbn [edenot]; ev_simpl E. rewrite Hsp. exact Hal.
      - apply krange_intro; cbn [edenot]; ev_simpl E. rewrite Hsp. flia.
      - apply (kwr_intro SEGS E mem (EVar 2) sp (-3584) 3584); [cbn [edenot]; ev_simpl E; exact Hsp | flia | flia | flia |].
        replace (bv_unsigned sp + -3584)%Z with (bv_unsigned sp - 3584)%Z by flia. exact Hstw.
      - apply kalign_intro; [flia|]. cbn [edenot]; ev_simpl E. exact P10.
      - apply krange_intro; cbn [edenot]; ev_simpl E. flia.
      - apply (kwr_intro SEGS E mem (EVar 64) Uw (-2928) 2984); [cbn [edenot]; ev_simpl E; reflexivity | flia | flia | flia |].
        eapply (proj2 (proj2 (proj2 (writable_at mem _ _ (bv_unsigned Uw + -2928) 2984 HB0 Hstw ltac:(flia) ltac:(flia) ltac:(flia) ltac:(flia) ltac:(flia))))).
      - cbn [kentry_ok]; unfold estart; cbn [a_base a_off edenot]; ev_simpl E; rewrite Hsp; flia.
      - apply krange_intro; cbn [edenot]; ev_simpl E; rewrite u_small by flia; flia.
      - apply kalign_intro; [flia|]; cbn [edenot]; ev_simpl E; rewrite u_small by flia; exact P3.
      - apply krange_intro; cbn [edenot]; ev_simpl E; rewrite u_small by flia; flia.
      - apply krange_intro; cbn [edenot]; ev_simpl E; rewrite u_small by flia; flia.
      - kdisj_place.
      - kdisj_place.
      - kdisj_place.
      - kdisj_place.
    }
    pin_reg HR (4%bv:reg) (ELit TP) by (regv HR (4%bv:reg); exact Htp).
    pin_reg HR (11%bv:reg) (EVar 68) by (regv HR (11%bv:reg); exact Ha1).
    (* [comment removed for export] *)
    run_fp 30%nat [0x7ff58%Z] noscr true.
    kcell HK (EVar 2) (-8)%Z 8%nat (EVar 1) K1. kcell HK (EVar 2) (-16)%Z 8%nat (EVar 8) K2.
    kcell HK (EVar 2) (-24)%Z 8%nat (EVar 9) K3. kcell HK (EVar 2) (-32)%Z 8%nat (EVar 18) K4.
    kcell HK (EVar 2) (-40)%Z 8%nat (EVar 19) K5. kcell HK (EVar 2) (-48)%Z 8%nat (EVar 20) K6.
    kcell HK (EVar 2) (-56)%Z 8%nat (EVar 21) K7. kcell HK (EVar 2) (-64)%Z 8%nat (EVar 22) K8.
    kcell HK (EVar 2) (-72)%Z 8%nat (EVar 23) K9. kcell HK (EVar 2) (-80)%Z 8%nat (EVar 24) K10.
    kcell HK (EVar 2) (-88)%Z 8%nat (EVar 25) K11. kcell HK (EVar 2) (-96)%Z 8%nat (EVar 26) K12.
    kcell HK (EVar 2) (-104)%Z 8%nat (EVar 27) K13.
    lazymatch goal with |- runs_to _ (@mkst _ _ _ ?M1 _) _ =>
      assert (HS1 : SAVED13 M1) by
        (unfold SAVED13;
         repeat match goal with |- _ /\ _ => split end;
         (lazymatch goal with |- cell64 _ _ (?a - ?k)%Z _ => replace (a - k)%Z with (a + - k)%Z by flia end; cbn [Z.opp]; unfold cell64, LibDefs.cell; rewrite ?Hra; assumption))
    end.
    clear K1 K2 K3 K4 K5 K6 K7 K8 K9 K10 K11 K12 K13.
    log_frameF [(SA (EVar 2) (-160), 160%Z)] Hfr1. rewrite Hsp in Hfr1.
    pin_reg HR (2%bv:reg) (EVar 64) by (regv HR (2%bv:reg); cbn [edenot]; ev_simpl E; rewrite Hsp; reflexivity).
    assert (HI1 : EINV M).
    { split; [exact HS1|]. split; [eapply frame_BIGF_app; [exact HB0 | exact Hfr1 | apply bincl_of; constructor; [cbn [fst snd]; apply in_stack; flia | constructor]]|].
      split; [eapply acellw_frame; [exact Hfr1 | exact Hh0 | flia | flia | solve_apart]|].
      split; [intros i Hi Hni; unfold FS_FLAGS0_LEN in Hi; unfold FS_FLAGS0; rewrite (byte_frame mem M _ (fs + 4096 + i) Hfr1 ltac:(flia)); [apply Hfl0; exact Hi | solve_apart]|].
      split; [intros i Hi Hni; rewrite (byte_frame mem M _ (fs + 0x8c00 + i) Hfr1 ltac:(flia)); [apply Hfl5; flia | solve_apart]|].
      destruct Hgfr as [gb Hgb]. destruct (cell_of_rdn SEGS mem GF 4 gb Hgb ltac:(flia)) as [gw Hgw]. exists gw.
      eapply cell_frame; [exact Hfr1 | exact Hgw | flia | cbn; flia | solve_apart]. }
    assert (Hh5a : acellw SEGS M (fs + 40) h5) by (eapply acellw_frame; [exact Hfr1 | exact Hh5 | flia | flia | solve_apart]).
    assert (Hfa0 : M (Z_to_bv 64 fa) = Some (Z_to_bv 8 0)).
    { rewrite P2. rewrite (byte_frame mem M _ (fs + 35840 + pos) Hfr1 ltac:(flia)); [apply Hfl5; flia | solve_apart]. }
    clear HS1 Hfr1.
    (* [comment removed for export] *)
    run_fp 30%nat [0x3ca74%Z] noscr false.
    pose proof HI1 as (_ & HB1 & _).
    eapply rt_call.
    { eapply (Hsm5 fs h5 (CH ctx thr t48 t56 dtls v24) _ _ _ rom (Z_to_bv 64 0x7ff88)).
      - regv HR (1%bv:reg); reflexivity.
      - apply ret_ok_even; rewrite u_small by flia; reflexivity.
      - unfold stkmalloc_pre; cbv zeta; cbn [al_abi as_both aa_tp both_abi].
        rewrite <- pos_eq, <- F_eq, <- fa_eq. replace (fs + 8 * 5)%Z with (fs + 40)%Z by flia. change (2048 / 8)%Z with 256%Z. unfold AS_SB.
        split; [regv HR (4%bv:reg); reflexivity|].
        split; [exact (as_env_bigf M HB1)|].
        split; [exact (fs_hdr_bigf M HB1)|].
        split; [exact Hh5a|].
        split; [exact Hfa0|].
        split; [eapply (writable_at M _ _ (fs + 40) 8 HB1 Hwh5); flia|].
        split; [eapply (writable_at M _ _ fa 1 HB1 Hwfl5); flia|].
        split; [eapply (writable_at M _ _ F 2048 HB1 Hwfr5); flia|].
        split; [eapply (writable_at M _ _ (SB + F / 8) 256 HB1 Hwsf5); unfold SB in *; flia|].
        exists Uw. split; [regv HR (2%bv:reg); reflexivity|].
        unfold as_frame, stackish. split; [flia|]. split; [apply (mod_down (bv_unsigned Uw) 16 2); [flia|flia|exact P10]|].
        eapply (writable_at M _ _ (bv_unsigned Uw - 208) 208 HB1 Hstw); flia. }
    cbv beta. intros FQ1 rq1 mq1 (Hkeep & Hfkeep & Hpost).
    unfold stkmalloc_post in Hpost; cbv zeta in Hpost. rewrite <- pos_eq, <- F_eq, <- fa_eq in Hpost.
    replace (fs + 8 * 5)%Z with (fs + 40)%Z in Hpost by flia. change (2048 / 8)%Z with 256%Z in Hpost. unfold AS_SB in Hpost.
    replace (F + 2048 - 8)%Z with (F + 2040)%Z in Hpost by flia.
    destruct Hpost as (Ha0F & Hfr2 & _ & Hfa).
    lazymatch type of HR with regs_ok _ _ ?Rx =>
      assert (HX : getr Rx 2 = Uw) by (regv HR (2%bv:reg); reflexivity); rewrite HX in Hfr2; clear HX end.
    unfold regs_kept in Hkeep. unfold fregs_kept in Hfkeep. after_call Hkeep Hfkeep FQ1. clear Hkeep Hfkeep.
    kframe HK Hfr2 [(SA (EVar 64) (-208), 208%Z); (SA (EVar 67) 40, 8%Z); (SA (EVar 66) 0, 1%Z); (SA (EVar 65) 24, 8%Z);
                    (SA (EVar 65) 2040, 8%Z); (SA (EAlu ALU_SRL (EVar 65) (ELit 3)) SB, 256%Z)].
    assert (HI2 : EINV mq1).
    { eapply EINV_frame; [exact HI1 | exact Hfr2 | apply bincl_of; repeat (apply Forall_cons); try apply Forall_nil; cbn [fst snd];
        [apply in_stack; flia | apply in_hint5 | rewrite P2; apply in_flags5; flia | apply in_frames5; flia | apply in_frames5; flia | apply in_shframes5; unfold SB; flia] |..];
        unfold SB; solve_apart. }
    pose proof HI2 as (_ & HB2 & _). clear HI1 HB1 Hfr2 Hh5a Hfa0.
    (* [comment removed for export] *)
    pin_reg HR (10%bv:reg) (EVar 65) by (regv HR (10%bv:reg); cbn [edenot]; ev_simpl_goal; exact Ha0F).
    kn_prefix HK [KWr (SA (EVar 65) 0) 2048; KWr (SA (EAlu ALU_SRL (EVar 65) (ELit 3)) SB) 256].
    { apply (kwr_intro SEGS _ mq1 (EVar 65) (Z_to_bv 64 F) 0 2048);
        [cbn [edenot]; ev_simpl_goal; reflexivity | rewrite u_small by flia; flia | flia | rewrite u_small by flia; flia |
         rewrite u_small by flia; eapply (proj2 (proj2 (proj2 (writable_at mq1 _ _ (F + 0) 2048 HB2 Hwfr5 ltac:(flia) ltac:(flia) ltac:(flia) ltac:(flia) ltac:(flia)))))]. }
    { replace SB with (SB + 0)%Z at 1 by flia. eapply (kwr_shadow_intro SEGS _ mq1 (EVar 65) (Z_to_bv 64 F) 0 256);
        [cbn [edenot]; ev_simpl_goal; reflexivity | flia | flia | rewrite u_small by flia; unfold SB in *; flia |
         rewrite u_small by flia; eapply (proj2 (proj2 (proj2 (writable_at mq1 _ _ (SB + F / 8 + 0) 256 HB2 Hwsf5 ltac:(unfold SB; flia) ltac:(unfold SB; flia) ltac:(flia) ltac:(unfold SB; flia) ltac:(unfold SB; flia)))))]. }
    (* [comment removed for export] *)
    run_fp 60%nat [0x54040%Z] noscr true.
    log_frameF [(SA (EVar 64) 24, 8%Z); (SA (EVar 64) 48, 8%Z); (SA (EVar 65) 0, 24%Z); (SA (EAlu ALU_SRL (EVar 65) (ELit 3)) SB, 8%Z)] Hfr3.
    kcell HK (EVar 64) 24%Z 8%nat (ELit SB) C24.
    lazymatch goal with |- runs_to _ (@mkst _ _ _ ?Mx _) _ =>
      assert (HI3 : EINV Mx);
      [ eapply EINV_frame; [exact HI2 | exact Hfr3 | apply bincl_of; repeat (apply Forall_cons); try apply Forall_nil; cbn [fst snd];
          [apply in_stack; flia | apply in_stack; flia | apply in_frames5; flia | apply in_shframes5; unfold SB; flia] |..]; unfold SB; solve_apart |];
      assert (Hfa3 : acell SEGS Mx (F + 2040) 8 fa) by (eapply acell_frame; [exact Hfr3 | exact Hfa | flia | cbn; flia | unfold SB; solve_apart]) end.
    pose proof HI3 as (_ & HB3 & _). clear HI2 HB2 Hfr3 Hfa.
    eapply rt_call.
    { eapply (Hsf8 (Z_to_bv 64 (SF + 8)) _ _ _ rom (Z_to_bv 64 0x80030)).
      - regv HR (1%bv:reg); reflexivity.
      - apply ret_ok_even; rewrite u_small by flia; reflexivity.
      - unfold setsh_pre. cbn [al_abi as_both].
        split; [regv HR (10%bv:reg); sfreg|].
        split; [regv HR (11%bv:reg); reflexivity|].
        split; [rewrite u_small by (unfold SB in *; flia); apply mod_add_multiple; [flia | exact P9 | reflexivity]|].
        split; [rewrite u_small by (unfold SB in *; flia); eapply (writable_at _ _ _ (SB + F / 8 + 8) 122 HB3 Hwsf5); unfold SB in *; flia|].
        exact (proj1 (as_env_bigf _ HB3)). }
    cbv beta. intros FQ2 rq2 mq2 (Hkeep & Hfkeep & Hfr4). unfold setshf8_post in Hfr4.
    unfold regs_kept in Hkeep. unfold fregs_kept in Hfkeep. after_call Hkeep Hfkeep FQ2. clear Hkeep Hfkeep.
    kframe HK Hfr4 [(SA (EAlu ALU_SRL (EVar 65) (ELit 3)) (SB + 8), 122%Z)].
    assert (HI4 : EINV mq2).
    { eapply EINV_frame; [exact HI3 | exact Hfr4 | apply bincl_of; constructor; [cbn [fst snd]; apply in_shframes5; unfold SB; flia | constructor] |..]; unfold SB; solve_apart. }
    assert (Hfa4 : acell SEGS mq2 (F + 2040) 8 fa) by (eapply acell_frame; [exact Hfr4 | exact Hfa3 | flia | cbn; flia | unfold SB; solve_apart]).
    assert (C24b : cell64 SEGS mq2 (bv_unsigned Uw + 24) (Z_to_bv 64 SB)) by (eapply cell64_frame; [exact Hfr4 | exact C24 | flia | flia | unfold SB; solve_apart]).
    pose proof HI4 as (_ & HB4 & _). clear HI3 HB3 Hfr4 Hfa3 C24.
    (* [comment removed for export] *)
    run_fp 60%nat [0x53f20%Z] noscr true.
    log_frameF [(SA (EAlu ALU_SRL (EVar 65) (ELit 3)) (SB + 130), 26%Z)] Hfr5.
    lazymatch goal with |- runs_to _ (@mkst _ _ _ ?Mx _) _ =>
      assert (HI5 : EINV Mx);
      [ eapply EINV_frame; [exact HI4 | exact Hfr5 | apply bincl_of; constructor; [cbn [fst snd]; apply in_shframes5; unfold SB; flia | constructor] |..]; unfold SB; solve_apart |];
      assert (Hfa5 : acell SEGS Mx (F + 2040) 8 fa) by (eapply acell_frame; [exact Hfr5 | exact Hfa4 | flia | cbn; flia | unfold SB; solve_apart]);
      assert (C24c : cell64 SEGS Mx (bv_unsigned Uw + 24) (Z_to_bv 64 SB)) by (eapply cell64_frame; [exact Hfr5 | exact C24b | flia | flia | unfold SB; solve_apart]) end.
    pose proof HI5 as (_ & HB5 & _). clear HI4 HB4 Hfr5 Hfa4 C24b.
    eapply rt_call.
    { eapply (Hs00 (Z_to_bv 64 (SF + 8)) _ _ _ rom (Z_to_bv 64 0x800a8)).
      - regv HR (1%bv:reg); reflexivity.
      - apply ret_ok_even; rewrite u_small by flia; reflexivity.
      - unfold setsh_pre. cbn [al_abi as_both].
        split; [regv HR (10%bv:reg); sfreg|].
        split; [regv HR (11%bv:reg); reflexivity|].
        split; [rewrite u_small by (unfold SB in *; flia); apply mod_add_multiple; [flia | exact P9 | reflexivity]|].
        split; [rewrite u_small by (unfold SB in *; flia); eapply (writable_at _ _ _ (SB + F / 8 + 8) 122 HB5 Hwsf5); unfold SB in *; flia|].
        exact (proj1 (as_env_bigf _ HB5)). }
    cbv beta. intros FQ3 rq3 mq3 (Hkeep & Hfkeep & Hfr6 & Hz6). unfold setsh00_post in Hfr6. rewrite u_small in Hz6 by (unfold SB in *; flia).
    unfold regs_kept in Hkeep. unfold fregs_kept in Hfkeep. after_call Hkeep Hfkeep FQ3. clear Hkeep Hfkeep.
    kframe HK Hfr6 [(SA (EAlu ALU_SRL (EVar 65) (ELit 3)) (SB + 8), 122%Z)].
    assert (HI6 : EINV mq3).
    { eapply EINV_frame; [exact HI5 | exact Hfr6 | apply bincl_of; constructor; [cbn [fst snd]; apply in_shframes5; unfold SB; flia | constructor] |..]; unfold SB; solve_apart. }
    assert (Hfa6 : acell SEGS mq3 (F + 2040) 8 fa) by (eapply acell_frame; [exact Hfr6 | exact Hfa5 | flia | cbn; flia | unfold SB; solve_apart]).
    assert (C24d : cell64 SEGS mq3 (bv_unsigned Uw + 24) (Z_to_bv 64 SB)) by (eapply cell64_frame; [exact Hfr6 | exact C24c | flia | flia | unfold SB; solve_apart]).
    Ltac Zify.zify_post_hook ::= Z.div_mod_to_equations.
    assert (HF64 : ((F + 64) / 8 = F / 8 + 8)%Z) by (clear -P4; flia).
    Ltac Zify.zify_post_hook ::= idtac.
    assert (HshP : shz mq3 P 122).
    { split; [apply F8k; reflexivity|]. intros j Hj. rewrite HF64. replace (SB + (F / 8 + 8) + j)%Z with (SB + F / 8 + 8 + j)%Z by flia. apply Hz6. exact Hj. }
    pose proof HI6 as (_ & HB6 & _). clear HI5 HB5 Hfr6 Hfa5 C24c Hz6.
    (* [comment removed for export] *)
    Ltac Zify.zify_post_hook ::= Z.div_mod_to_equations.
    assert (HF32 : ((F + 32) / 8 = F / 8 + 4)%Z) by (clear -P4; flia).
    Ltac Zify.zify_post_hook ::= idtac.
    run_fp 30%nat [0x81c30%Z] noscr true.
    lazymatch goal with EQM : ?Mn = mem_denot ?E2 ?Mo ?log, HLF : log_flat _ _, HK : know_ok _ _ _ ?kn |- _ =>
      assert (HshQ : shz Mn (F + 32) 1);
      [ split; [apply F8k; reflexivity|]; intros j Hj;
        pose proof (mem_denot_lzK_cover SEGS E2 _ kn Mo log (EAlu ALU_SRL (EVar 65) (ELit 3)) (SB + 4) 1 HK HLF ltac:(vm_compute; reflexivity)) as HZ;
        rewrite EQM;
        rewrite edenot_srl3 in HZ; cbn [edenot] in HZ; ev_simpl_in E2 HZ; rewrite u_small in HZ by flia;
        rewrite HF32; replace (SB + (F / 8 + 4) + j)%Z with (F / 8 + (SB + 4 + j))%Z by flia;
        apply HZ; unfold SB; cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; flia | ] end.
    log_frameF [(SA (EAlu ALU_SRL (EVar 65) (ELit 3)) (SB + 4), 1%Z); (SA (EVar 65) 32, 8%Z)] Hfr7.
    kcell_auto HK (EVar 65) 32%Z 4%nat CQ0. kcell_auto HK (EVar 65) 36%Z 4%nat CQ4.
    lazymatch goal with |- runs_to _ (@mkst _ _ _ ?Mx _) _ =>
      assert (HI7 : EINV Mx);
      [ eapply EINV_frame; [exact HI6 | exact Hfr7 | apply bincl_of; constructor; [cbn [fst snd]; apply in_shframes5; unfold SB; flia | constructor; [cbn [fst snd]; apply in_frames5; flia | constructor]] |..]; unfold SB; solve_apart |];
      assert (Hfa7 : acell SEGS Mx (F + 2040) 8 fa) by (eapply acell_frame; [exact Hfr7 | exact Hfa6 | flia | cbn; flia | unfold SB; solve_apart]);
      assert (C24e : cell64 SEGS Mx (bv_unsigned Uw + 24) (Z_to_bv 64 SB)) by (eapply cell64_frame; [exact Hfr7 | exact C24d | flia | flia | unfold SB; solve_apart]);
      assert (HshP7 : shz Mx P 122) by (eapply shz_frame; [exact Hfr7 | exact HshP | flia | flia | rewrite HF64; unfold SB; solve_apart]) end.
    pose proof HI7 as (HS7 & HB7 & Hh07 & Hfl07 & Hf57 & Hgw7). clear HI6 HB6 Hfr7 Hfa6 C24d HshP.
    (* [comment removed for export] *)
    assert (HP64 : ((F + 64) mod 64 = 0)%Z) by (apply mod_add_multiple; [flia | apply (mod_down F 64 32); [flia|flia|exact P3] | reflexivity]).
    assert (Hq8 : ((F + 32) mod 8 = 0)%Z) by (apply F8k; reflexivity).
    lazymatch goal with |- runs_to _ (@mkst ?I ?Rx _ ?Mx _) _ =>
    assert (REST : cell32 SEGS Mx (F + 32) 0 /\ cell32 SEGS Mx (F + 32 + 4) 1 /\ ((F + 32) mod 8 = 0)%Z /\ heapish ceil (F + 32) 8 /\ shz Mx (F + 32) 1 /\
      (fs + FS_FRAMES5 <= F + 32)%Z /\ (F + 32 + 8 <= fs + FS_SIZE)%Z /\ (F + 32 + 8 <= F + 64 \/ F + 64 + 976 <= F + 32)%Z /\
      writable SEGS Mx (F + 64) 976 /\ ((F + 64) mod 64 = 0)%Z /\ heapish ceil (F + 64) 976 /\ shz Mx (F + 64) 122 /\
      (fs + FS_FRAMES5 <= F + 64)%Z /\ (F + 64 + 976 <= fs + FS_SIZE)%Z /\
      as_frame SEGS ceil Mx Uw PARSE_DB /\ shz Mx (bv_unsigned Uw - PARSE_DB) (PARSE_DB / 8) /\
      as_env SEGS ceil both_abi fs (CH ctx thr t48 t56 dtls v24) Mx /\ fs_hdr SEGS ceil both_abi fs Mx /\ fs_writable SEGS fs Mx /\
      (exists h, acellw SEGS Mx (fs + FS_HINT0) h) /\ fs_flags0_but fs [] Mx)
    end.
    { split; [split; [flia | exact CQ0]|]. split; [split; [flia | replace (F + 32 + 4)%Z with (F + 36)%Z by flia; exact CQ4]|].
      split; [exact Hq8|]. split; [unfold heapish; plc|]. split; [exact HshQ|].
      unfold FS_FRAMES5, FS_SIZE, PARSE_DB. split; [flia|]. split; [flia|]. split; [flia|].
      split; [eapply (writable_at _ _ _ (F + 64) 976 HB7 Hwfr5); flia|]. split; [exact HP64|]. split; [unfold heapish; plc|].
      split; [exact HshP7|]. split; [flia|]. split; [flia|].
      split. { unfold as_frame, stackish. split; [flia|]. split; [apply (mod_down (bv_unsigned Uw) 16 2); [flia|flia|exact P10]|].
               eapply (writable_at _ _ _ (bv_unsigned Uw - 2928) 2928 HB7 Hstw); flia. }
      split. { change (2928 / 8)%Z with 366%Z. eapply (shz_sub _ _ _ _ _ (stsh_bigf _ HB7)); [apply mod_sub_multiple; [flia | apply (mod_down _ 8 4); [flia|flia|exact P10] | reflexivity] | flia | flia | change (DEPTH / 8)%Z with 448%Z; flia]. }
      split; [exact (as_env_bigf _ HB7)|]. split; [exact (fs_hdr_bigf _ HB7)|]. split; [exact (fs_writable_bigf _ HB7)|].
      split; [exists h0; exact Hh07|]. exact Hfl07. }
    (* [comment removed for export] *)
    Ltac finish_parse FQ rq mq Hpost :=
      lazymatch goal with HR : regs_ok _ _ ?Rx, HF : fregs_ok _ _ _, HK : know_ok _ _ _ _ |- _ =>
      lazymatch type of Hpost with _ =>
        let Hkeep := fresh "Hkeep" in let Hfkeep := fresh "Hfkeep" in let Hfr := fresh "Hfr8" in
        let Hfl := fresh "Hfl08" in let h' := fresh "h'" in let Hh := fresh "Hh08" in let r := fresh "r" in
        let Hr10 := fresh "Hr10" in let Hr01 := fresh "Hr01" in let HPr := fresh "HPr" in
        destruct Hpost as (Hkeep & Hfkeep & Hfr & Hfl & [h' Hh] & [r (Hr10 & Hr01 & HPr)]);
        rewrite !u_small in HPr by flia;
        unfold regs_kept in Hkeep; unfold fregs_kept in Hfkeep; after_call Hkeep Hfkeep FQ; clear Hkeep Hfkeep;
        lazymatch goal with HR' : regs_ok _ _ rq, HS7 : SAVED13 ?Mx, HB7 : frame_mod mem _ BIGF, C24e : cell64 _ _ _ _, Hfa7 : acell _ _ _ 8 fa,
                             Hf57 : flags5_but _, HshP7 : shz _ P 122, Hgw7 : (exists gw, _) |- _ =>
          pose proof (after_parse Mx mq h' HS7 HB7 C24e Hfa7 Hf57 HshP7 Hgw7 Hfr Hfl Hh) as HMB;
          apply (phaseA1 FQ rq mq r);
          [ split; [regv HR' (2%bv:reg); reflexivity|];
            split; [regv HR' (9%bv:reg); reflexivity|];
            split; [regv HR' (8%bv:reg); rewrite_getr; reflexivity|];
            split; [regv HR' (3%bv:reg); reflexivity|];
            split; [regv HR' (4%bv:reg); rewrite_getr; reflexivity|];
            split; [regv HR' (19%bv:reg); sfreg|];
            split; [regv HR' (21%bv:reg); sfreg|];
            split; [regv HR' (25%bv:reg); reflexivity|];
            split; [regv HR' (18%bv:reg); reflexivity|];
            split; [regv HR' (27%bv:reg); apply bv_eq; vm_compute; reflexivity|];
            exact HMB
          | regv HR' (20%bv:reg); rewrite alu_add_lit, u_small by flia; reflexivity
          | exact Hr10
          | exact Hr01
          | first [exact HPr | intros Hr1; exfalso; exact (parsed_ok_len0 _ _ _ _ (HPr Hr1))] ]
        end end end.
    destruct (Z.eq_dec n 0) as [Hn0|Hn0].
    - eapply rt_call.
      { eapply (Hparse0 Uw (Z_to_bv 64 (F + 32)) (Z_to_bv 64 (F + 64)) fs (CH ctx thr t48 t56 dtls v24) _ _ _ rom (Z_to_bv 64 0x800d0)).
        + regv HR (1%bv:reg); reflexivity.
        + apply ret_ok_even; rewrite u_small by flia; reflexivity.
        + unfold parse_pre0. cbv zeta. rewrite !u_small by flia.
          split; [regv HR (2%bv:reg); reflexivity|]. split; [regv HR (11%bv:reg); rewrite Hn0; reflexivity|].
          split; [regv HR (12%bv:reg); rewrite alu_add_lit, u_small by flia; reflexivity|]. split; [regv HR (13%bv:reg); reflexivity|].
          split; [regv HR (14%bv:reg); rewrite alu_add_lit, u_small by flia; reflexivity|]. split; [regv HR (4%bv:reg); reflexivity|].
          exact REST. }
      cbv beta. intros FQ4 rq4 mq4 Hpost. unfold parse_post_bo in Hpost.
      finish_parse FQ4 rq4 mq4 Hpost.
    - eapply rt_call.
      { eapply (Hparse data n bs Uw (Z_to_bv 64 (F + 32)) (Z_to_bv 64 (F + 64)) fs (CH ctx thr t48 t56 dtls v24) _ _ _ rom (Z_to_bv 64 0x800d0)).
        + regv HR (1%bv:reg); reflexivity.
        + apply ret_ok_even; rewrite u_small by flia; reflexivity.
        + unfold parse_pre_bo. cbv zeta. cbn [al_abi as_both]. rewrite !u_small by flia.
          split; [regv HR (2%bv:reg); reflexivity|]. split; [regv HR (10%bv:reg); exact Ha0|]. split; [regv HR (11%bv:reg); reflexivity|].
          split; [regv HR (12%bv:reg); rewrite alu_add_lit, u_small by flia; reflexivity|]. split; [regv HR (13%bv:reg); reflexivity|].
          split; [regv HR (14%bv:reg); rewrite alu_add_lit, u_small by flia; reflexivity|]. split; [regv HR (4%bv:reg); reflexivity|].
          pose proof (data_bigf _ HB7 ltac:(flia)) as [HD1 HD2].
          split; [exact HD1|]. split; [exact HD2|].
          exact REST. }
      cbv beta. intros FQ4 rq4 mq4 Hpost. unfold parse_post_bo in Hpost.
      finish_parse FQ4 rq4 mq4 Hpost.
  Qed.

  Theorem fuzz_Q : exists (FP' : FPState) regs' mem',
    msteps SEGS (mkst (FP:=FP0) regs (Z_to_bv 64 0x7ff14) mem rom) (mkst (FP:=FP') regs' ret mem' rom) /\
    getr regs' 10 = Z_to_bv 64 0 /\
    (forall r, In r fuzz_kept -> getr regs' r = getr regs r) /\
    frame_mod mem mem' BIGF /\
    azero mem' (fs + FS_FLAGS0) FS_FLAGS0_LEN /\ azero mem' (fs + FS_FLAGS5) FS_FLAGS5_LEN.
  Proof.
    destruct entry_run as (st' & Hms & (FP' & regs' & mem' & -> & H)).
    exists FP', regs', mem'. split; [exact Hms | exact H].
  Qed.
End Proof.