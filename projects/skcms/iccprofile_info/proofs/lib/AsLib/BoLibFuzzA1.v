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
  Lemma phaseE : forall (FPX : FPState) R M, BASE R M ->
    runs_to SEGS (mkst (FP:=FPX) R (Z_to_bv 64 0x8030c) M rom) Q.
  Proof.
    intros FPX R M HB. pose proof HB as (R2 & R9 & R8 & R3 & R4 & R19 & R21 & R25 & R18 & R27 & HMB).
    pose proof HMB as (M1 & M2 & M3 & M4 & M5 & M6 & M7 & M8 & M9). destruct M9 as [gw Hgw].
    need_nums. need_regs. need_wr. pose proof placement as PL.
    pose proof PL as (P0 & P1 & P2 & P3 & P4 & P5 & P6 & P7 & P8 & P9 & P10 & P11 & P12 & P13 & P14 & _). clear PL.
    unfold FS_FRAMES5, FS_FRAMES_LEN, FS_SHFRAMES_LEN, FS_FLAGS5, FS_FLAGS5_LEN, FS_FLAGS0, FS_FLAGS0_LEN, AS_SB in Hwfr5, Hwsf5, Hwfl5, Hwfl0, Hstw.
    pose proof (u64_range sp) as Hspr.
    destruct (packB R (fp_regs (FPState:=FPX)) M gw [] HB Hgw) as (HR & HF & HK & _ & H64).
    pose proof (H64 : id _) as H64i. clear H64. unfold KNB in HK.
    run_fp 10%nat [0x54040%Z] noscr false.
    (* [comment removed for export] *)
    eapply rt_call.
    { eapply (Hsf8 (Z_to_bv 64 (SF + 8)) _ _ _ rom (Z_to_bv 64 0x80318)).
      - regv HR (1%bv:reg); reflexivity.
      - apply ret_ok_even; rewrite u_small by flia; reflexivity.
      - unfold setsh_pre. cbn [al_abi as_both].
        split; [regv HR (10%bv:reg); sfreg|].
        split; [regv HR (11%bv:reg); reflexivity|].
        split; [rewrite u_small by (unfold SB in *; flia); apply mod_add_multiple; [flia | exact P9 | reflexivity]|].
        split; [rewrite u_small by (unfold SB in *; flia);
                eapply (writable_at M _ _ (SB + F / 8 + 8) 122 M2 Hwsf5); unfold SB in *; flia|].
        exact (proj1 (as_env_bigf M M2)). }
    cbv beta. intros FQ1 rq1 mq1 (Hkeep & Hfkeep & Hfr1). unfold setshf8_post in Hfr1.
    unfold regs_kept in Hkeep. unfold fregs_kept in Hfkeep. after_call Hkeep Hfkeep FQ1. clear Hkeep Hfkeep.
    kframe HK Hfr1 [(SA (EAlu ALU_SRL (EVar 97) (ELit 3)) (SB + 8), 122%Z)].
    assert (HB1 : frame_mod mem mq1 BIGF)
      by (eapply frame_BIGF_app; [exact M2 | exact Hfr1 |]; apply bincl_of; constructor; [|constructor]; cbn [fst snd];
          apply in_shframes5; flia).
    assert (HS1 : SAVED13 mq1) by (eapply SAVED13_frame; [exact M1 | exact Hfr1 | unfold SB in *; solve_apart]).
    assert (C24a : cell64 SEGS mq1 ((bv_unsigned Uw) + 24) (Z_to_bv 64 SB)) by (eapply cell64_frame; [exact Hfr1 | exact M3 | flia | flia | unfold SB in *; solve_apart]).
    assert (C40a : acell SEGS mq1 (F + 2040) 8 fa) by (eapply acell_frame; [exact Hfr1 | exact M4 | flia | cbn; flia | unfold SB in *; solve_apart]).
    assert (F0a : fs_flags0_but fs [] mq1).
    { intros i Hi Hni. unfold FS_FLAGS0, FS_FLAGS0_LEN in *. rewrite (byte_frame M mq1 _ (fs + 4096 + i) Hfr1 ltac:(flia)); [apply M5; assumption|]. unfold SB in *; solve_apart. }
    assert (F5a : flags5_but mq1).
    { intros i Hi Hni. rewrite (byte_frame M mq1 _ (fs + 0x8c00 + i) Hfr1 ltac:(flia)); [apply M7; assumption|]. unfold SB in *; solve_apart. }
    clear Hfr1 M1 M2 M3 M4 M5 M6 M7 M8 Hgw.
    (* [comment removed for export] *)
    run_fp 10%nat [0x3cc80%Z] noscr true.
    log_frameF [(SA (EVar 97) 0, 8%Z)] Hfr2.
    lazymatch goal with |- runs_to _ (@mkst _ _ _ ?Mx _) _ =>
      assert (HB2 : frame_mod mem Mx BIGF)
        by (eapply frame_BIGF_app; [exact HB1 | exact Hfr2 |]; apply bincl_of; constructor; [|constructor]; cbn [fst snd]; apply in_frames5; flia);
      assert (HS2 : SAVED13 Mx) by (eapply SAVED13_frame; [exact HS1 | exact Hfr2 | solve_apart]);
      assert (C40b : acell SEGS Mx (F + 2040) 8 fa) by (eapply acell_frame; [exact Hfr2 | exact C40a | flia | cbn; flia | solve_apart]);
      assert (F0b : fs_flags0_but fs [] Mx) by
        (intros i Hi Hni; unfold FS_FLAGS0, FS_FLAGS0_LEN in *; rewrite (byte_frame mq1 Mx _ (fs + 4096 + i) Hfr2 ltac:(flia)); [apply F0a; assumption|]; solve_apart);
      assert (F5b : flags5_but Mx) by
        (intros i Hi Hni; rewrite (byte_frame mq1 Mx _ (fs + 0x8c00 + i) Hfr2 ltac:(flia)); [apply F5a; assumption|]; solve_apart)
    end.
    clear Hfr2 HB1 HS1 C24a C40a F0a F5a.
    eapply rt_call.
    { lazymatch goal with |- fn_contract _ _ _ _ -> _ => idtac | _ => idtac end.
      eapply (Hsf5 (Z_to_bv 64 F) (Z_to_bv 64 fa) _ _ _ rom (Z_to_bv 64 0x80334)).
      - regv HR (1%bv:reg); reflexivity.
      - apply ret_ok_even; rewrite u_small by flia; reflexivity.
      - unfold stkfree5_pre. cbn [al_abi as_both]. rewrite !u_small by flia.
        split; [regv HR (10%bv:reg); reflexivity|].
        split; [exact P3|].
        split; [unfold heapish; plc|].
        split; [exact C40b|].
        split; [unfold heapish; plc|].
        split; [eapply (writable_at _ _ _ fa 1 HB2 Hwfl5); flia|].
        split; [unfold AS_SB; eapply (writable_at _ _ _ (SB + F / 8) 256 HB2 Hwsf5); unfold SB in *; flia|].
        split; [exact (proj1 (as_env_bigf _ HB2))|].
        split; [exact (proj1 (proj2 (proj2 (as_env_bigf _ HB2))))|].
        exists Uw. split; [regv HR (2%bv:reg); reflexivity|].
        unfold as_frame, stackish. split; [flia|]. split; [apply (mod_down (bv_unsigned Uw) 16 2); [flia|flia|exact P10]|].
        eapply (writable_at _ _ _ ((bv_unsigned Uw) - 16) 16 HB2 Hstw); flia. }
    cbv beta. intros FQ2 rq2 mq2 (Hkeep & Hfkeep & Hfr3 & Hfa0). unfold stkfree5_post in Hfr3.
    lazymatch type of HR with regs_ok _ _ ?Rx =>
      assert (HR2x : getr Rx 2 = Uw) by (regv HR (2%bv:reg); reflexivity); rewrite HR2x in Hfr3; clear HR2x end.
    rewrite !u_small in Hfr3 by (flia). unfold AS_SB in Hfr3.
    unfold regs_kept in Hkeep. unfold fregs_kept in Hfkeep. after_call Hkeep Hfkeep FQ2. clear Hkeep Hfkeep.
    kframe HK Hfr3 [(SA (EVar 96) (-16), 16%Z); (SA (EVar 98) 0, 1%Z); (SA (EAlu ALU_SRL (EVar 97) (ELit 3)) SB, 256%Z)].
    lazymatch type of Hfr3 with frame_mod ?Ma ?Mb _ =>
      assert (HB3 : frame_mod mem Mb BIGF)
        by (eapply frame_BIGF_app; [exact HB2 | exact Hfr3 |]; apply bincl_of; repeat (apply Forall_cons); try apply Forall_nil; cbn [fst snd];
            [apply in_stack; flia | apply in_flags5; flia | apply in_shframes5; unfold SB; flia]);
      assert (HS3 : SAVED13 Mb) by (eapply SAVED13_frame; [exact HS2 | exact Hfr3 | unfold SB in *; solve_apart]);
      assert (F0c : fs_flags0_but fs [] Mb) by
        (intros i Hi Hni; unfold FS_FLAGS0, FS_FLAGS0_LEN in *; rewrite (byte_frame Ma Mb _ (fs + 4096 + i) Hfr3 ltac:(flia)); [apply F0b; assumption|]; unfold SB in *; solve_apart);
      assert (F5c : azero Mb (fs + FS_FLAGS5) FS_FLAGS5_LEN)
    end.
    { unfold FS_FLAGS5, FS_FLAGS5_LEN. intros i Hi. destruct (Z.eq_dec i pos) as [->|Hne].
      - rewrite <- P2. exact Hfa0.
      - lazymatch type of Hfr3 with frame_mod ?Ma ?Mb _ =>
          rewrite (byte_frame Ma Mb _ (fs + 35840 + i) Hfr3 ltac:(flia)); [apply F5b; [flia|exact Hne]|]; unfold SB in *; solve_apart end. }
    run_fp 40%nat (@nil Z) noscr false.
    fin_ret.
    unfold Q.
    lazymatch goal with |- exists _ _ _, @mkst ?I ?R' _ ?M' _ = _ /\ _ => exists I, R', M' end.
    split; [regv HR (1%bv:reg); rewrite_getr; reflexivity|].
    split; [regv HR (10%bv:reg); reflexivity|].
    split; [| split; [exact HB3 | split; [| exact F5c]]].
    - lift_id H64i HR.
      exact (regs_same_on _ _ _ regs _ fuzz_kept H64i HR ltac:(vm_compute; reflexivity)).
    - intros i Hi. apply F0c; [exact Hi | intros []].
  Qed.
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
  Lemma phaseC : forall (FPX : FPState) R M, BASE R M ->
    getr R 20 = Z_to_bv 64 P -> (0 < n)%Z ->
    parsed_ok SEGS M data n bs P -> cell32 SEGS M (P + 460) 3 ->
    runs_to SEGS (mkst (FP:=FPX) R (Z_to_bv 64 0x80298) M rom) Q.
  Proof.
    intros FPX R M HB R20 Hn0 HP Hoc. pose proof HB as (R2 & R9 & R8 & R3 & R4 & R19 & R21 & R25 & R18 & R27 & HMB).
    pose proof HMB as (_ & _ & _ & _ & _ & _ & _ & _ & [gw Hgw]).
    need_nums. need_regs. pose proof placement as PL.
    pose proof PL as (P0 & P1 & P2 & P3 & P4 & P5 & P6 & P7 & P8 & P9 & P10 & P11 & P12 & P13 & P14 & _). clear PL.
    pose proof (u64_range sp) as Hspr.
    destruct (packB R (fp_regs (FPState:=FPX)) M gw [] HB Hgw) as (HR & HF & HK & _ & H64).
    pose proof (H64 : id _) as H64i. clear H64. unfold KNB in HK.
    apply (regs_ok_pin _ _ R 20 (EAlu ALU_ADD (EVar 97) (ELit 64))) in HR;
      [| cbn [edenot]; ev_simpl_goal; rewrite alu_add_lit, u_small by flia; rewrite R20; apply (f_equal (Z_to_bv 64)); flia].
    kn_prefix HK [KWord (SA (EVar 97) 524) 4 (ELit 3)].
    { destruct Hoc as [_ Hoc]. eapply (kword_intro SEGS _ M (EVar 97) (Z_to_bv 64 F) 524 4 (ELit 3) (Z_to_bv 64 3));
        [cbn [edenot]; ev_simpl_goal; reflexivity | reflexivity | flia | flia | rewrite u_small by flia; flia | rewrite u_small by flia; cbn; flia
        | rewrite u_small by flia; replace (F + 524)%Z with (F + 64 + 460)%Z by flia; exact Hoc]. }
    clear Hgw Hoc.
    run_fp 60%nat [0x803c4%Z] noscr false.
    call_rte 0x802b8%Z 312%Z.
    run_fp 60%nat [0x803c4%Z] noscr false.
    call_rte 0x802b8%Z 344%Z.
    run_fp 60%nat [0x803c4%Z] noscr false.
    call_rte 0x802b8%Z 376%Z.
    run_fp 60%nat [0x803c4%Z] noscr false.
    call_rte 0x802f0%Z 464%Z.
    run_fp 60%nat [0x803c4%Z] noscr false.
    call_rte 0x802f0%Z 496%Z.
    run_fp 60%nat [0x803c4%Z] noscr false.
    call_rte 0x802f0%Z 528%Z.
    run_fp 60%nat [0x8030c%Z] noscr true.
    log_frameF [(SA (ELit 0) GF, 4%Z)] Hfrg. change (0 + 0x5da040)%Z with 0x5da040%Z in Hfrg.
    kcell_auto HK (ELit 0) 0x5da040%Z 4%nat HG. rewrite ?u_small in HG by flia. change (0 + 0x5da040)%Z with 0x5da040%Z in HG.
    lazymatch goal with |- runs_to _ (@mkst _ _ _ ?Mn _) _ =>
      pose proof (MEMB_gf _ Mn HMB Hfrg ltac:(eexists; exact HG)) as HMBn; clear HMB; rename HMBn into HMB end.
    apply phaseE. base_now H64i.
  Qed.

  (* [comment removed for export] *)
  Lemma KND_pos : (0 < n)%Z -> KND = [KRange (EAlu ALU_ADD (EVar 74) (EVar 100)) 0 (2 ^ 47 - 2048); KRange (EVar 74) 1 (2 ^ 47 - 2048); KShad (EVar 74) (EVar 100) SB; KBlobD (SA (EVar 74) 0) (EVar 100) 0].
  Proof. intros Hn0. unfold KND. destruct (Z.ltb_spec 0 n); [reflexivity | exfalso; flia]. Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma phaseB2 : forall (FPX : FPState) R M (g8 g16 : word) (G : Z), BASE R M ->
    getr R 20 = Z_to_bv 64 P -> getr R 12 = Z_to_bv 64 G -> (0 < n)%Z ->
    parsed_ok SEGS M data n bs P -> cell32 SEGS M (P + 460) 3 ->
    cell64 SEGS M (P + 288) g8 -> cell64 SEGS M (P + 296) g16 ->
    (bv_unsigned g8 <> 0%Z -> inDATA data n (bv_unsigned g8) G) ->
    (bv_unsigned g16 <> 0%Z -> inDATA data n (bv_unsigned g16) (2 * G)) ->
    (1 <= G <= 12684751875)%Z ->
    runs_to SEGS (mkst (FP:=FPX) R (Z_to_bv 64 0x801f4) M rom) Q.
  Proof.
    intros FPX R M g8 g16 G HB R20 R12 Hn0 HP Hoc Hg8 Hg16 Hin8 Hin16 HG.
    pose proof HB as (R2 & R9 & R8 & R3 & R4 & R19 & R21 & R25 & R18 & R27 & HMB).
    pose proof HMB as (_ & HM2 & _ & _ & _ & _ & _ & _ & [gw Hgw]).
    need_nums. need_regs. pose proof placement as PL.
    pose proof PL as (P0 & P1 & P2 & P3 & P4 & P5 & P6 & P7 & P8 & P9 & P10 & P11 & P12 & P13 & P14 & _). clear PL.
    pose proof (u64_range sp) as Hspr. pose proof (u64_range g8) as Hg8r. pose proof (u64_range g16) as Hg16r. pose proof (u64_range data) as Hdr.
    destruct (data_bigf M HM2 Hn0) as ((HD1 & HD2 & HD3 & HD4) & Hdar). pose proof HD1 as (D1 & D2 & D3 & D4 & D5).
    unfold heapish in HD2. app_facts.
    destruct (packB R (fp_regs (FPState:=FPX)) M gw [g8; g16; Z_to_bv 64 G] HB Hgw) as (HR & HF & HKB & HKD & H64).
    pose proof (H64 : id _) as H64i. clear H64. rewrite (KND_pos Hn0) in HKD.
    apply (regs_ok_pin _ _ R 20 (EAlu ALU_ADD (EVar 97) (ELit 64))) in HR;
      [| cbn [edenot]; ev_simpl_goal; rewrite alu_add_lit, u_small by flia; rewrite R20; apply (f_equal (Z_to_bv 64)); flia].
    apply (regs_ok_pin _ _ R 12 (EVar 104)) in HR; [| cbn [edenot ev eb vals_ev blobs_ev nth app junk_vals fjunk_vals]; exact R12].
    unfold cell64, LibDefs.cell in Hg8, Hg16.
    lazymatch type of HR with regs_ok ?E _ _ =>
    assert (HK : know_ok SEGS E M
      ((if Z.eq_dec (bv_unsigned g8) 0 then KRange (EVar 102) 0 0 else KRange (EVar 102) 1 (2 ^ 47 - 16)) ::
       (if Z.eq_dec (bv_unsigned g16) 0 then KRange (EVar 103) 0 0 else KRange (EVar 103) 1 (2 ^ 47 - 16)) ::
       KWord (SA (EVar 97) 352) 8 (EVar 102) :: KWord (SA (EVar 97) 360) 8 (EVar 103) ::
       KRange (EVar 104) 1 12684751875 :: KNB ++ [KRange (EAlu ALU_ADD (EVar 74) (EVar 100)) 0 (2 ^ 47 - 2048); KRange (EVar 74) 1 (2 ^ 47 - 2048); KShad (EVar 74) (EVar 100) SB; KBlobD (SA (EVar 74) 0) (EVar 100) 0]));
    [ constructor; [destruct (Z.eq_dec _ 0); apply krange_intro; cbn [edenot]; ev_simpl E; [flia|];
                    destruct (Hin8 ltac:(assumption)) as (A1 & A2 & A3); flia |];
      constructor; [destruct (Z.eq_dec _ 0); apply krange_intro; cbn [edenot]; ev_simpl E; [flia|];
                    destruct (Hin16 ltac:(assumption)) as (A1 & A2 & A3); flia |];
      constructor; [eapply (kword_intro SEGS E M (EVar 97) (Z_to_bv 64 F) 352 8 (EVar 102) g8);
        [cbn [edenot]; ev_simpl E; reflexivity | cbn [edenot]; ev_simpl E; reflexivity | flia | flia | rewrite u_small by flia; flia | rewrite u_small by flia; cbn; flia |
         rewrite u_small by flia; replace (F + 352)%Z with (F + 64 + 288)%Z by flia; exact Hg8] |];
      constructor; [eapply (kword_intro SEGS E M (EVar 97) (Z_to_bv 64 F) 360 8 (EVar 103) g16);
        [cbn [edenot]; ev_simpl E; reflexivity | cbn [edenot]; ev_simpl E; reflexivity | flia | flia | rewrite u_small by flia; flia | rewrite u_small by flia; cbn; flia |
         rewrite u_small by flia; replace (F + 360)%Z with (F + 64 + 296)%Z by flia; exact Hg16] |];
      constructor; [apply krange_intro; cbn [edenot]; ev_simpl E; rewrite u_small by flia; flia |];
      exact (know_ok_app SEGS E M KNB _ HKB HKD)
    | clear HKB HKD ]
    end.
    unfold KNB in HK. cbn [app] in HK.
    destruct (Z.eq_dec (bv_unsigned g8) 0) as [Z8|NZ8]; [|specialize (Hin8 NZ8); unfold inDATA in Hin8];
    destruct (Z.eq_dec (bv_unsigned g16) 0) as [Z16|NZ16]; try (specialize (Hin16 NZ16); unfold inDATA in Hin16);
      run_fp 100%nat [0x80298%Z] noscr false.
    all: apply phaseC; [base_now H64i | creg (20%bv:reg) | exact Hn0 | exact HP | exact Hoc].
  Qed.
End Proof.
