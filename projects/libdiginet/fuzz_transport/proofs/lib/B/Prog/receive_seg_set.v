(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: restates text of projects/cgif/cgif_file_fuzzer/proofs/lib/YCbq.v:528-543, 616-634;
   projects/cgif/cgif_rgb_fuzzer/proofs/lib/YC05.v:41-45, 208-214, 230-234, for libreac/fuzz_identity's asan-ubsan build
   (lib/B). The same text also appears in projects/cgif/cgif_file_fuzzer/proofs/lib/YCbo.v:420-423, 430-444, 447-448,
   453-455, 470-475, 477-486, 489-491, 502-505, 511-514, 1255-1258. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_identity/lib/B/Prog/reac_box_name_seg_rel.v, with its module paths, module names and numbers changed; 329 of its 374 lines of code are new or changed and 1879 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libdiginet/fuzz_transport/lib/A/Prog/TickEpi.v, with its module paths and module names changed; 554 of its 607 lines of code are new or changed and 321 lines of the source are left out. *)
(* receive_seg_set: the last piece of the image-B walk of receive (lib/B/Prog/receive_seg_cut.v), Lemma recv_set :
   recv_set_stmt, from the set cut RECV_SET (+0x158, 0x83800) to receive's return at +0x184 (0x8382c). The code
   (offsets from AF_receive, listing lib/B/Prog/DgnTransportBList.v):
     +0x158          `mv a0, s2`: a0 = ticked (s2 at the cut, recv_regs_set);
     +0x15c          `jal settle` (return address +0x160 = 0x83808): settle_cg.v transport_settle_cg, a donor-form
                     callee lifted into the caller's G journal by TransportGCg.v gx_call_cg (G_HARNESS_gx_ok /
                     G_HARNESS_gx_noerrno, carried in recv_laws), from sp = the entry sp - 128, with tw_at at B3,
                     settle_m B3 ticked = Some (Bw', tt), invariant (2) of TRunInv.run_inv B3 and no event. Its X
                     gives Bw' = B3; its gx_kept carries the world relation (TWorldB.v tw_kept_GB); its acall_kept_g,
                     stated at its call state (the caller's blocks with the frame's block), folds into the cut's by
                     dk_kept_trans_nf_g with no own frame; its window lies below the six saved words, which it keeps;
     +0x160          `mv a0, s0`: a0 = a, the block the malloc returned;
     +0x164          `jal` the free wrapper (return address +0x168 = 0x83810 = RECV_RA_FREE): lib/A/Prog/
                     receive_seg_alloc.v gx_free_at (YC5d.v afree04_rule in the G journal) at pc_wrap_free
                     (recv_laws), o = the entry sp - 128 - sp0, ra = 0x83810, chain [] (s0 = the heap block, below
                     that sp: YG00.v bad_next, rsb_chain_nil), the FIXED trace of recv_fix (gx_trace0 at the empty
                     chain), the footprint premise by gx_start_fp (the block is none of the caller's: the blocks are
                     pairwise apart, sep_blocks_pos) and the meter by mok_station;
     +0x168 .. +0x17c  the six reloads `ld ra, s0 .. s4` of the words the prologue saved (recv_cur's RECV_SAVED, at
                     sp + 120 .. sp + 80 = the entry sp - 8 .. - 48, above both callees' windows and outside the
                     block, so settle and the free keep them): each register gets back its entry value;
     +0x180          `addi sp, sp, 128`: sp = the entry sp;
     +0x184          `ret`, taken by lib/B/Prog/DgnTransportBPaLib.v paj_ret_at: the return is receive's.
   The three stretches of straight code are runs of the token engine over the G journal (TransportGRunB.v paj_run_x)
   from a symbolic state whose only region is the six saved words (read only, rsb_entry); each run stops at its call
   (the two jal) or at the `ret`, and writes no memory (rsb_KA_step).
   The post: transport_recv_post with two events, the callee-saved registers the reloads' (and gp, tp, s5 .. s11
   never written), the block removed from the blocks (Permutation), the free's acall_kept folded with
   dk_kept_trans_nf_g (its written range is the block, apart from the caller's blocks and frames: rsb_blk_apart,
   rsb_blk_frames), the meter charged the malloc, 0 and the free, and X at the malloc's address a: receive_m's Bw'
   (recv_res), the world relation at Bw' = B3 (G kept by settle and the free: gx_kept_of_acall_kept) and
   g_fail_next Bw' <= 1. *)
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s YK0o.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import YN3v YI04 YI00 YI08 YG0s.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq YC5d.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import YM05 YImgTop.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require YI16 YI5b YI5c.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import PaTable PaSym PaStep PaRun PaShadow PaJournal.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require YC4b receive_seg_alloc receive_seg_set.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import
DgnTransportBSyms DgnTransportBList DgnTransportBAddr DgnTransportBPa DgnTransportBImg DgnTransportBPaLib YC1g YC1h.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B Require Import YB1v Img0.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B Require YE2k AsanCells TransportGB.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A Require Import W_journalG.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import TransportGCg TransportRtCg TWorldG.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import DgnTransportBCg TransportGRunB.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import TWorldB TImgB.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import m_set_cg check_state_data_cg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import send_control_cg send_data_cg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import diginet_body_check_cg set_state_cg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import diginet_session_wake_cg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import on_ack_cg on_data_cg on_announce_cg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import diginet_frame_parse_cg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import diginet_session_tick_cg diginet_session_rx_cg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import m_tick_cg m_rx_cg io_recv_cg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import spec_read_frame_cg settle_cg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import diginet_session_poll_cg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import receive_cg receive_seg_cut.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel Require TWorld TCb TImg TSess0 TSess TOps TRunInv.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.
Module YK11 := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YK11.
Module TG := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.TransportGB.
Module TW := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TWorld.
Module TC := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TCb.
Module AALLOC := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog.receive_seg_alloc.
Module ASET := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog.receive_seg_set.
#[global] Remove Hints OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5b.src0_sink_head
  OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5c.src0_sink
  OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5c.src0_sink_laws : typeclass_instances.

(* ------------------------------------------------------------------ *)
(* 1. The symbolic state of the three runs                             *)
(* ------------------------------------------------------------------ *)

(* Atoms: 0 .. 31 the registers at the run's start, 32 the shadow base (no shadow entry: no instrumented check on
   this code), 33 .. 38 the entry values of ra, s0, s1, s2, s3, s4 (RECV_SAVED, in its order). The one region: the
   six saved words at sp + 80 .. sp + 128 (sp = the entry sp - 128, atom 2), read only. *)
Definition rsb_rg_sv : YP09.region :=
  YP09.mkRegion (Some 2%nat) 80 128 0 0
    [YP09.mkChunk 120 (CVal 8 (SOff 33 0)); YP09.mkChunk 112 (CVal 8 (SOff 34 0));
     YP09.mkChunk 104 (CVal 8 (SOff 35 0)); YP09.mkChunk 96 (CVal 8 (SOff 36 0));
     YP09.mkChunk 88 (CVal 8 (SOff 37 0)); YP09.mkChunk 80 (CVal 8 (SOff 38 0))].
Definition rsb_regions : smem := [rsb_rg_sv].
Definition rsb_facts : facts := mkFacts [] [] [].
Definition ss_rsb (pc : Z) : sstate := mkSS pc sr_atoms rsb_regions None rsb_facts.
Definition RSB_SH : list shent := [].
Definition RSB_Bx : sv := SOff 32 0.
(* The three run starts: the set cut (+0x158), settle's return (+0x160), the free's return (+0x168), and the `ret`
   the last run stops at (+0x184). *)
Lemma rsb_pcs : RECV_SET = 9568 /\ AF_receive + 0x160 = 9576 /\ AF_receive + 0x168 = 9584 /\
  AF_receive + 0x184 = 9612.
Proof. repeat split; reflexivity. Qed.

(* The values of atoms 32 .. 38. *)
Definition rsb_extra (regs : bvmap 5 word) : list word :=
  Z_to_bv 64 SHADOW_OFF :: map (fun o : Z * Z => YK11.getr regs (Z_to_bv 5 (snd o))) RECV_SAVED.

(* The write rights of a run from a state with rsb_regions: no region has a writable byte. *)
Ltac rsb_awr :=
  lazymatch goal with |- awr_ok_x ?Ex ?rs ?Gx ?XO ?OUT ?stk ?sp0q ?fp ?b0 ?bc ?lyq ?ownq =>
    let rs' := eval vm_compute in rs in change (awr_ok_x Ex rs' Gx XO OUT stk sp0q fp b0 bc lyq ownq) end;
  repeat (apply awr_ok_x_cons;
    [ let a := fresh "a" in let Ha := fresh "Ha" in intros a Ha;
      cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha; lia |]);
  apply awr_ok_x_nil.

(* The value of register r in the machine state of HS: its symbolic value, computed, then tac. *)
Ltac rsb_reg HS r v H tac :=
  lazymatch type of HS with
  | st_ok_pi ?segsx ?vl ?Ex ?ssx (restrict ?Hh ?msx) =>
      let e := eval vm_compute in (sr_get (ss_regs ssx) r) in
      assert (H : YK11.getr (ms_regs msx) r = v) by
        (refine (eq_trans (st_ok_pi_restrict_reg Hh Ex ssx msx r HS) _); change (sv_denot Ex e = v); tac)
  | OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YP0l.st_ok ?segsx ?Ex ?ssx (restrict ?Hh ?msx) =>
      let e := eval vm_compute in (sr_get (ss_regs ssx) r) in
      assert (H : YK11.getr (ms_regs msx) r = v) by
        (refine (eq_trans (st_ok_restrict_reg segsx Hh Ex ssx msx r HS) _); change (sv_denot Ex e = v); tac)
  | ?T => idtac "rsb_reg: no match for" T; fail
  end.

(* s0 below sp: the chain the allocator walks is empty (YG00.v bad_next). *)
Lemma rsb_chain_nil : forall ly rd (regsT : bvmap 5 word),
  4096 <= raZ regsT -> s0Z regsT <= spZ regsT -> chain_pre ly rd regsT [].
Proof.
  intros ly rd regsT Hra Hs. unfold chain_pre. split; [exact Hra|].
  destruct (frame0_ok ly regsT); [|reflexivity].
  unfold bad_next. replace (s0Z regsT <=? spZ regsT) with true by (symmetry; apply Z.leb_le; exact Hs).
  reflexivity.
Qed.

Section e. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Local Abbreviation segs := tfibsegs.
Local Abbreviation VAL := (@pa_val _ transportb_listing PI_transportb).
Local Abbreviation BASE := (@pa_val _ transportb_listing PI_transportb A_TEXT).

Definition rsb_E (regsX regs : bvmap 5 word) : env := Eimg (PI := PI_transportb) (Ereg regsX (rsb_extra regs)).

Lemma rsb_ew_reg : forall regsX regs n (r : bv 5), Z.of_nat n = bv_unsigned r ->
  ew (rsb_E regsX regs) n = YK11.getr regsX r.
Proof. intros regsX regs n r Hn. unfold rsb_E. apply ew_Eimg_Ereg_nat. exact Hn. Qed.

Lemma rsb_ew_saved : forall regsX regs,
  ew (rsb_E regsX regs) 33 = YK11.getr regs (Z_to_bv 5 1) /\ ew (rsb_E regsX regs) 34 = YK11.getr regs (Z_to_bv 5 8) /\
  ew (rsb_E regsX regs) 35 = YK11.getr regs (Z_to_bv 5 9) /\ ew (rsb_E regsX regs) 36 = YK11.getr regs (Z_to_bv 5 18) /\
  ew (rsb_E regsX regs) 37 = YK11.getr regs (Z_to_bv 5 19) /\ ew (rsb_E regsX regs) 38 = YK11.getr regs (Z_to_bv 5 20).
Proof.
  intros regsX regs.
  assert (EX : forall j, (j < 7)%nat -> ew (rsb_E regsX regs) (32 + j) = nth j (rsb_extra regs) (Z_to_bv 64 0))
    by (intros j Hj; unfold rsb_E; rewrite Eimg_low by (unfold A_TEXT; lia); apply ew_Ereg_extra).
  pose proof (EX 1%nat ltac:(lia)) as E1. pose proof (EX 2%nat ltac:(lia)) as E2.
  pose proof (EX 3%nat ltac:(lia)) as E3. pose proof (EX 4%nat ltac:(lia)) as E4.
  pose proof (EX 5%nat ltac:(lia)) as E5. pose proof (EX 6%nat ltac:(lia)) as E6.
  cbn [Nat.add nth rsb_extra map RECV_SAVED snd] in E1, E2, E3, E4, E5, E6.
  repeat split; assumption.
Qed.

Lemma rsb_agree : forall regsX regs, env_agree 32 (Ereg regsX (rsb_extra regs)) (rsb_E regsX regs).
Proof. intros regsX regs. split; [intros n Hn; unfold rsb_E; apply Eimg_low; unfold A_TEXT; lia | reflexivity]. Qed.

(* A saved word read back as the chunk of its atom. *)
Lemma rsb_chunk : forall E (H : word -> bool) (mem : word -> option byte) (b off : Z) (n : nat) (x : word),
  ew E n = x -> rdword (aview segs H mem) (b + off) = Some (bv_unsigned x) ->
  YP09.chunk_ok segs E (mrestrict H mem) b (YP09.mkChunk off (CVal 8 (SOff n 0))).
Proof.
  intros E H mem b off n x Hx Hw.
  apply (chunk_ok_val segs E _ b off 8 (SOff n 0) (bv_unsigned x)).
  - cbn [sv_denot]. rewrite Hx, Z.add_0_r. reflexivity.
  - pose proof (bv_unsigned_in_range 64 x) as Hrr. change (bv_modulus 64) with (2 ^ 64) in Hrr. exact Hrr.
  - zside.
  - exact (val_mem_of_rdword segs _ _ _ _ Hw).
Qed.

(* The symbolic state at pc (the set cut +0x158, or +0x160 after settle, or +0x168 after the free) holds of the
   machine state there: sp is the entry sp - 128 and the six saved words hold the entry registers. *)
Lemma rsb_entry : forall (W : world segs) (regsX regs : bvmap 5 word) mem pc,
  YK11.getr regsX (Z_to_bv 5 2) = Z_to_bv 64 (spZ regs - 128) ->
  YM05.alloc_ceiling <= spZ regs - 128 -> spZ regs <= 2 ^ 47 ->
  Forall (fun o : Z * Z => rdword (aview segs (w_H W) mem) (spZ regs - fst o) =
      Some (bv_unsigned (YK11.getr regs (Z_to_bv 5 (snd o))))) RECV_SAVED ->
  st_ok_pi segs VAL (rsb_E regsX regs) (ss_rsb pc)
    (restrict (w_H W) (@YK11.mkst fx regsX (Z_to_bv 64 (BASE + pc)) mem (YK11.seg_rom segs))).
Proof.
  intros W regsX regs mem pc R2 Hce H47 Hsaved.
  pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
  set (E := rsb_E regsX regs).
  assert (U2 : bv_unsigned (ew E 2) = spZ regs - 128).
  { unfold E. rewrite (rsb_ew_reg regsX regs 2 (Z_to_bv 5 2) eq_refl), R2. apply unsigned_lit_small. lia. }
  destruct (rsb_ew_saved regsX regs) as (X33 & X34 & X35 & X36 & X37 & X38).
  fold E in X33, X34, X35, X36, X37, X38.
  unfold RECV_SAVED in Hsaved.
  apply Forall_cons_iff in Hsaved as [Sra Hsaved]. apply Forall_cons_iff in Hsaved as [Ss0 Hsaved].
  apply Forall_cons_iff in Hsaved as [Ss1 Hsaved]. apply Forall_cons_iff in Hsaved as [Ss2 Hsaved].
  apply Forall_cons_iff in Hsaved as [Ss3 Hsaved]. apply Forall_cons_iff in Hsaved as [Ss4 _].
  cbn [fst snd] in Sra, Ss0, Ss1, Ss2, Ss3, Ss4.
  rewrite restrict_mkst_fx. unfold ss_rsb.
  apply (@pa_entry_st_ok_full fx rc transportb_listing PI_transportb).
  - apply regs_ok_Eimg_Ereg.
  - vm_compute. reflexivity.
  - apply Forall_cons; [|apply Forall_nil]. unfold rsb_rg_sv, region_ok.
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val]. rewrite U2.
    split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
    apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons;
      [|apply Forall_cons; [|apply Forall_nil]]]]]].
    + apply (rsb_chunk E (w_H W) mem (spZ regs - 128) 120 33 _ X33).
      replace (spZ regs - 128 + 120) with (spZ regs - 8) by lia. exact Sra.
    + apply (rsb_chunk E (w_H W) mem (spZ regs - 128) 112 34 _ X34).
      replace (spZ regs - 128 + 112) with (spZ regs - 16) by lia. exact Ss0.
    + apply (rsb_chunk E (w_H W) mem (spZ regs - 128) 104 35 _ X35).
      replace (spZ regs - 128 + 104) with (spZ regs - 24) by lia. exact Ss1.
    + apply (rsb_chunk E (w_H W) mem (spZ regs - 128) 96 36 _ X36).
      replace (spZ regs - 128 + 96) with (spZ regs - 32) by lia. exact Ss2.
    + apply (rsb_chunk E (w_H W) mem (spZ regs - 128) 88 37 _ X37).
      replace (spZ regs - 128 + 88) with (spZ regs - 40) by lia. exact Ss3.
    + apply (rsb_chunk E (w_H W) mem (spZ regs - 128) 80 38 _ X38).
      replace (spZ regs - 128 + 80) with (spZ regs - 48) by lia. exact Ss4.
  - cbn [pairwise_disjoint all_disjoint rsb_regions]. split; exact I.
  - unfold rsb_facts, facts_ok. cbn [f_atoms f_conds f_alias atoms_ok conds_ok alias_ok].
    repeat match goal with |- _ /\ _ => split end; exact I.
Qed.

(* What a run keeps, from its start memory m0 to a memory m: every byte's view, and presence. *)
Definition rsb_KA (W : world segs) (m0 m : word -> option byte) : Prop :=
  (forall a, aview segs (w_H W) m a = aview segs (w_H W) m0 a) /\
  (forall a, apresent (w_H W) m0 a -> apresent (w_H W) m a).

Lemma rsb_KA_refl : forall (W : world segs) m, rsb_KA W m m.
Proof. intros W m. split; [intros a; reflexivity | intros a Ha; exact Ha]. Qed.

(* A run from a state with rsb_regions writes nothing. *)
Lemma rsb_KA_step : forall E (W : world segs) m0 (m m' : word -> option byte),
  rsb_KA W m0 m ->
  frame_of E rsb_regions (mrestrict (w_H W) m) (mrestrict (w_H W) m') ->
  mem_grows (mrestrict (w_H W) m) (mrestrict (w_H W) m') ->
  rsb_KA W m0 m'.
Proof.
  intros E W m0 m m' [K1 K2] Hfr Hg. split.
  - assert (Hw : forall b wlo whi x, In (b, wlo, whi) (windows rsb_regions) ->
      base_val E b + wlo <= x < base_val E b + whi -> (fun _ : Z => False) x).
    { intros b wlo whi x Hin Hx.
      lazymatch type of Hin with In ?y ?l => let l' := eval vm_compute in l in change (In y l') in Hin end.
      cbn [In] in Hin.
      repeat (destruct Hin as [Hin | Hin]; [injection Hin as <- <- <-; exfalso; lia |]).
      destruct Hin. }
    intros a.
    rewrite (aview_wrap64 segs (w_H W) m' a), (aview_wrap64 segs (w_H W) m0 a).
    rewrite (YC4b.kept_of_frame E rsb_regions (w_H W) m m' (fun _ => False) Hfr Hw (a mod 2 ^ 64)
      ltac:(apply Z.mod_pos_bound; lia) (fun x => x)).
    exact (K1 (a mod 2 ^ 64)).
  - intros a Ha. exact (apresent_grows _ _ _ a Hg (K2 a Ha)).
Qed.

(* The six saved words, carried to another memory that keeps [sp - 48, sp). *)
Lemma rsb_saved_ext : forall (W W' : world segs) (m m' : word -> option byte) (sp : Z) (regs : bvmap 5 word),
  Forall (fun o : Z * Z => rdword (aview segs (w_H W) m) (sp - fst o) =
      Some (bv_unsigned (YK11.getr regs (Z_to_bv 5 (snd o))))) RECV_SAVED ->
  (forall x, sp - 48 <= x < sp -> aview segs (w_H W') m' x = aview segs (w_H W) m x) ->
  Forall (fun o : Z * Z => rdword (aview segs (w_H W') m') (sp - fst o) =
      Some (bv_unsigned (YK11.getr regs (Z_to_bv 5 (snd o))))) RECV_SAVED.
Proof.
  intros W W' m m' sp regs HS HK.
  assert (HSB : Forall (fun o : Z * Z => 8 <= fst o <= 48) RECV_SAVED)
    by (unfold RECV_SAVED; repeat apply Forall_cons; try apply Forall_nil; cbn [fst]; lia).
  apply Forall_forall. intros o Hoin. cbv beta.
  pose proof (proj1 (Forall_forall _ _) HS o Hoin) as Ho.
  pose proof (proj1 (Forall_forall _ _) HSB o Hoin) as Hb.
  cbn beta in Ho, Hb.
  rewrite (rdword_ext (aview segs (w_H W) m) (aview segs (w_H W') m') (sp - fst o)); [exact Ho|].
  intros k0 Hk0. apply HK. lia.
Qed.

Variable B : asyms.

(* What a run kept, as an acall_kept_g with an empty window. *)
Lemma rsb_kept_g : forall G ly S (W : world segs) m0 m s (Eo : Z -> Prop),
  rsb_KA W m0 m -> acall_kept_g segs B G ly S W m0 W m s s Eo.
Proof.
  intros G ly S W m0 m s Eo [K1 K2]. unfold acall_kept_g.
  split; [intros; apply K1|]. split; [intros; apply K1|]. split; [intros; apply K1|].
  split; [intros; apply K1|]. split; [intros a _ _ Ha; exact (K2 a Ha)|]. intros a Ha. lia.
Qed.

Hypothesis LAWS : AR_laws segs B.

(* A block listed first in a permutation of the live blocks is apart from every other listed block. *)
Lemma rsb_blk_apart : forall ly S (W : world segs) m md (p nb : Z) rest b mm i,
  AR segs B ly S W m md -> Permutation (ablocks B ly S) ((p, nb) :: rest) -> In (b, mm) rest ->
  0 <= i < req_size mm -> p <= b + i < p + req_size nb -> False.
Proof.
  intros ly S W m md p nb rest b mm i HAR HP Hin Hi Hx.
  destruct (ASET.rs_perm_two _ _ _ _ HP Hin) as (l1 & l2 & l3 & [E | E]);
    pose proof (sep_blocks_pos segs B LAWS ly S W m md _ _ l1 l2 l3 HAR E) as D;
    unfold zdisjoint, block_rng in D; cbn [fst snd] in D; lia.
Qed.

(* A live block is apart from the live side-stack frames and their shadow bytes. *)
Lemma rsb_blk_frames : forall ly2 S2 (W2 : world segs) m2 md2 lyc Sc p nb,
  AR segs B ly2 S2 W2 m2 md2 -> In (p, nb) (ablocks B ly2 S2) -> frames S2 = frames Sc ->
  (forall cid pos, frame_addr ly2 cid pos = frame_addr lyc cid pos) ->
  forall cid pos x, In (cid, pos) (frames Sc) ->
    (in_zr x (frame_rng lyc (cid, pos)) \/ in_zr x (shadow_addr (frame_addr lyc cid pos), fs_frame_bytes cid / 8)) ->
    p <= x < p + req_size nb -> False.
Proof.
  intros ly2 S2 W2 m2 md2 lyc Sc p nb HAR Hin Hfr FA cid pos x Hf Hr Hx.
  assert (Hf2 : In (cid, pos) (frames S2)) by (rewrite Hfr; exact Hf).
  pose proof (sep_block_frame segs B LAWS ly2 S2 W2 m2 md2 p nb cid pos HAR Hin Hf2) as D.
  destruct (al_blocks _ _ LAWS ly2 S2 W2 m2 md2 p nb HAR Hin) as (_ & H4096 & Hce & Happ & _).
  destruct (frames_bounds segs B LAWS ly2 S2 W2 m2 md2 cid pos HAR Hf2) as (F4096 & Fce & _).
  pose proof (fs_frame_bytes_nonneg cid) as Hfs.
  pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
  rewrite FA in D, F4096, Fce.
  unfold zdisjoint in D. cbn [fst snd] in D.
  destruct Hr as [Hr | Hr]; unfold in_zr, frame_rng in Hr; cbn [fst snd] in Hr.
  - lia.
  - pose proof (shadow_range_end (frame_addr lyc cid pos) (fs_frame_bytes cid) Hfs) as Hse.
    assert (Hd : (frame_addr lyc cid pos + fs_frame_bytes cid) / 8 <= 0x7fffff800000 / 8)
      by (apply Z.div_le_mono; lia).
    pose proof (Z.div_pos (frame_addr lyc cid pos) 8 ltac:(lia) ltac:(lia)) as Hd0.
    change (0x7fffff800000 / 8) with 0xffffff00000 in Hd.
    unfold in_app, shadow_addr, SHADOW_OFF, kLowShadowBeg in *. lia.
Qed.
End e.

(* After a run: the model generalized, the kept fact carried to the run's last memory, the run's frame facts
   dropped. *)
Ltac rsb_after KA HS :=
  lazymatch goal with |- SRr _ _ (mkCfg _ (with_vm_backing (m_vm_lazy ?m0) ?mt ?m0)) _ =>
    let md := fresh "mdw" in set (md := with_vm_backing (m_vm_lazy m0) mt m0) in *; clearbody md; clear mt end;
  lazymatch goal with HFr : frame_of _ _ (mrestrict _ _) (mrestrict _ _), HG : mem_grows _ _ |- _ =>
    let KA' := fresh "KAn" in
    pose proof (rsb_KA_step _ _ _ _ _ KA HFr HG) as KA'; clear KA HFr HG; rename KA' into KA end;
  lazymatch goal with HF : frame_of _ _ _ _ |- _ => clear HF end.

(* A register the walk keeps: its atom at the run's start, through the chain of aregs_preserved P to the cut's
   value Rr. *)
Ltac rsb_keep EE P rn rz Rr :=
  cbn [sv_denot]; rewrite (EE rn (Z_to_bv 5 rz) eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned;
  rewrite (P rz ltac:(unfold acallee_saved; lia)); exact Rr.
(* A register reloaded from a saved word: the atom X of the word. *)
Ltac rsb_sv X := cbn [sv_denot]; rewrite X, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity.

(* ------------------------------------------------------------------ *)
(* 2. The piece                                                        *)
(* ------------------------------------------------------------------ *)

Section s. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Local Abbreviation tfib_sink_head := YE2k.tfib_sink_head.
Variable B : asyms.
Variable MT : ameter_ops.
Local Abbreviation segs := tfibsegs.
Local Abbreviation VAL := (@pa_val _ transportb_listing PI_transportb).
Local Abbreviation BASE := (@pa_val _ transportb_listing PI_transportb A_TEXT).

Lemma recv_set : @recv_set_stmt fx rc B MT.
Proof.
unfold recv_set_stmt, recv_set_at.
intros LAWS0 CALLS STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs p by_poll pf T bytes Bw ch a Bw'
  ly2 S2 W2 mem2 md2 regs2 B3 ticked HFIX HCUR HRES HTW3 HGF3 HINV3 HSET Htk HREGS.
destruct LAWS0 as (HMPC & HFPC & HCELLS & HRC & HGU & HGE & HRU & HRE & LAWS & MTL & HGX & HGNE).
destruct CALLS as (_ & _ & _ & _ & _ & _ & _ & SETC & AFREE).
destruct HFIX as (HJ0 & Hret & Hra4 & Hgp & Htp & _ & _ & _ & _ & Hch & Hsp16 & Hwlo & Hwhi & _ & _ & Hn &
  _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hnev & _ & Hmo & Hcost & _ & Htrf).
destruct HCUR as (HJ2 & Hfr2 & Hperm2 & Hmo2 & HK2 & Hsaved & Ha4096).
destruct HRES as (Haddr & Hrm).
destruct HREGS as ((R2 & R3 & R4 & R21 & R22 & R23 & R24 & R25 & R26 & R27) & R8 & R18).
destruct HINV3 as (_ & HQ3 & _).
set (n := Z.max 1 (Z.of_nat (length bytes))) in *.
assert (HC' : mo_malloc MT n + mo_free MT <= T) by exact Hcost.
clear Hcost.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (EST : RECV_STK = 16512) by reflexivity.
assert (ESS : SETTLE_STK <= 16384) by (vm_compute; discriminate).
assert (ESS0 : 0 <= SETTLE_STK) by (vm_compute; discriminate).
assert (EAS : ASTACK = 16384) by reflexivity.
assert (EEV : RECV_EV = 2) by reflexivity.
assert (HBASE : BASE = 0x812a0) by (vm_compute; reflexivity).
(* the journal's stack facts and layouts *)
pose proof HJ0 as (_ & _ & (memS0 & HJi0 & _) & _). rewrite !Z.add_0_r in HJi0.
pose proof HJi0 as (HARc & Hly0 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hstk & _).
pose proof Hstk as (Hsp0a & Hstk0 & Hceil & Hslo & Hshi & H47 & _ & _ & Htop).
clear HJi0 memS0.
pose proof HJ2 as (_ & _ & (memS2 & HJi2 & _) & _). rewrite !Z.add_0_r in HJi2.
pose proof HJi2 as (HAR2 & Hly2 & _).
clear HJi2 memS2.
assert (FA2 : forall cid pos, frame_addr ly2 cid pos = frame_addr lyc cid pos).
{ intros cid pos. unfold frame_addr.
  destruct Hly0 as (_ & _ & _ & _ & _ & EF0 & _). destruct Hly2 as (_ & _ & _ & _ & _ & EF2 & _).
  rewrite EF0, EF2. reflexivity. }
assert (HSPB : YM05.alloc_ceiling + 16512 <= spZ regs <= 2 ^ 47) by (rewrite EST in Hwlo; lia).
assert (HCE : YM05.alloc_ceiling <= spZ regs - RECV_STK) by (rewrite EST; lia).
assert (Hn1 : 1 <= n) by (unfold n; lia).
(* the block, apart from the caller's blocks and frames, none of the caller's blocks *)
assert (INA2 : In (a, n) (ablocks B ly2 S2)) by (apply (Permutation_in _ (Permutation_sym Hperm2)); left; reflexivity).
assert (BL2 : forall bm, In bm (ablocks B lyc Sc) -> In bm (ablocks B ly2 S2))
  by (intros bm Hb; apply (Permutation_in _ (Permutation_sym Hperm2)); right; exact Hb).
assert (NFB : forall b m i, In (b, m) (ablocks B lyc Sc) -> 0 <= i < req_size m -> a <= b + i < a + req_size n -> False)
  by (intros b m i Hb Hi Hx; exact (rsb_blk_apart B LAWS ly2 S2 W2 mem2 md2 a n _ b m i HAR2 Hperm2 Hb Hi Hx)).
assert (NFF : forall cid pos x, In (cid, pos) (frames Sc) ->
    (in_zr x (frame_rng lyc (cid, pos)) \/ in_zr x (shadow_addr (frame_addr lyc cid pos), fs_frame_bytes cid / 8)) ->
    a <= x < a + req_size n -> False)
  by exact (rsb_blk_frames B LAWS ly2 S2 W2 mem2 md2 lyc Sc a n HAR2 INA2 Hfr2 FA2).
assert (FRESH : ~ In (a, n) (ablocks B lyc Sc)).
{ intros Hin. pose proof (req_size_pos n ltac:(lia)) as [Hr _].
  exact (NFB a n 0 Hin ltac:(lia) ltac:(lia)). }

(* ---- run 1, +0x158 .. +0x15c: a0 = ticked, the call of settle ---- *)
pose proof (@rsb_entry fx rc W2 regs2 regs mem2 RECV_SET ltac:(exact R2) ltac:(lia) ltac:(lia) Hsaved) as HS.
set (E1 := rsb_E regs2 regs) in HS.
assert (HEI1 : img_env VAL A_LIM E1) by (unfold E1, rsb_E; apply Eimg_env).
assert (EE1 : forall n0 (r : bv 5), Z.of_nat n0 = bv_unsigned r -> ew E1 n0 = YK11.getr regs2 r)
  by (intros n0 r Hn0; unfold E1; apply rsb_ew_reg; exact Hn0).
assert (SHOK1 : sh_ok segs RSB_Bx RSB_SH E1 (mrestrict (w_H W2) mem2)) by (unfold sh_ok, RSB_SH; apply Forall_nil).
pose proof (rsb_KA_refl W2 mem2) as KA1.
pose proof (@paj_run_x fx rc tfib_sink_head transportb_listing PL_transportb PI_transportb B LAWS TG.G_HARNESS_B HGX
  0 []) as RUN.
paj_run_tok RUN HS HJ2 SHOK1 YC4b.Bspan.
{ rsb_awr. }
rsb_after KA1 HS.
lazymatch type of HS with context [restrict _ ?m] => rename m into ms1 end.
pmkst HS.
rsb_reg HS (1%bv : bv 5) (Z_to_bv 64 (BASE + 9576)) R1a ltac:(apply codeptr_val; exact HEI1).
rsb_reg HS (Z_to_bv 5 2) (Z_to_bv 64 (spZ regs - 128)) Q2
  ltac:(cbn [sv_denot]; rewrite (EE1 2%nat (Z_to_bv 5 2) eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; exact R2).
rsb_reg HS (Z_to_bv 5 3) (YK11.getr regs (Z_to_bv 5 3)) Q3
  ltac:(cbn [sv_denot]; rewrite (EE1 3%nat (Z_to_bv 5 3) eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; exact R3).
rsb_reg HS (Z_to_bv 5 4) (YK11.getr regs (Z_to_bv 5 4)) Q4
  ltac:(cbn [sv_denot]; rewrite (EE1 4%nat (Z_to_bv 5 4) eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; exact R4).
rsb_reg HS (Z_to_bv 5 10) (Z_to_bv 64 ticked) Q10
  ltac:(cbn [sv_denot]; rewrite (EE1 18%nat (Z_to_bv 5 18) eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; exact R18).
assert (P1 : aregs_preserved regs2 (ms_regs ms1))
  by (apply (aregs_preserved_of_st_ok segs (w_H W2) E1 _ ms1 regs2 (rsb_extra regs) HS);
      [ exact (rsb_agree regs2 regs) | vm_compute; reflexivity ]).
assert (Hsp1 : spZ (ms_regs ms1) = spZ regs - 128).
{ change (bv_unsigned (YK11.getr (ms_regs ms1) (Z_to_bv 5 2)) = spZ regs - 128). rewrite Q2.
  apply unsigned_lit_small. lia. }
destruct KA1 as [KA1v KA1p].
assert (HTWc : tw_at TMAP_B (aview segs (w_H W2) (ms_mem ms1)) B3)
  by exact (tw_kept TMAP_B _ _ B3 HTW3 (fun x _ => KA1v x)).
assert (KC1 : acall_kept_g segs B TG.G_HARNESS_B lyc Sc W memc W2 (ms_mem ms1) (spZ regs - RECV_STK) (spZ regs)
  (recv_wr bytes)).
{ apply (dk_kept_trans_g segs B TG.G_HARNESS_B lyc Sc W memc W2 mem2 W2 (ms_mem ms1) (spZ regs - RECV_STK)
    (spZ regs) (spZ regs) (spZ regs) (recv_wr bytes) (fun _ => False) HCE ltac:(lia) HK2
    (rsb_kept_g B TG.G_HARNESS_B lyc Sc W2 mem2 (ms_mem ms1) (spZ regs) _ (conj KA1v KA1p))
    ltac:(lia) ltac:(lia) (fun x Hx => False_ind _ Hx)). }
lazymatch goal with |- SRr ?sg ?Wx (mkCfg (@YK11.mkst _ ?rg _ ?mm ?rom) ?mdx) ?Q =>
  change (SRr sg Wx (@cfg_at fx segs (transportb_sigma TB_settle) rg mm mdx) Q) end.
eapply SRr_bind.
{ apply (@gx_call_cg fx rc tfib_sink_head segs B MT TG.G_HARNESS_B STK sp0 FP ly S W0 mem0 md0 own ly2 S2 W2
    (ms_mem ms1) _ (k + 1) _ (ms_regs ms1) SETTLE_STK SETTLE_EV 0 (fun _ => False)
    (fun _ _ _ => Bw' = B3) HGX HGNE HJ2).
  intros memS HJS. eapply SRr_mono.
  { apply (SETC fx STK sp0 FP ly S W0 memS md0 own ly2 S2 W2 (ms_mem ms1) _ (k + 1) (ms_regs ms1) ticked B3 Bw' HJS).
    - rewrite R1a. apply (ret_ok_codeptr_v (PI := PI_transportb)); [lia | reflexivity].
    - change (4096 <= bv_unsigned (YK11.getr (ms_regs ms1) 1%bv)). rewrite R1a, HBASE.
      rewrite unsigned_lit_small by lia. lia.
    - exact (eq_trans Q3 Hgp).
    - exact (eq_trans Q4 Htp).
    - exact Q10.
    - lia.
    - rewrite Hsp1. replace (spZ regs - 128) with (spZ regs + (-8) * 16) by lia. rewrite Z_mod_plus_full.
      exact Hsp16.
    - rewrite Hsp1. rewrite EST in Hwlo. lia.
    - rewrite Hsp1. lia.
    - exact HTWc.
    - exact HSET.
    - exact HQ3.
    - unfold SETTLE_EV. rewrite EEV in Hnev. lia. }
  intros W' c' _ Hp. apply decode_cg_post_dcg. exact Hp. }
intros W3 c3 _ HPOST.
destruct HPOST as (ly3 & S3 & regs3 & mem3 & md3 & e & -> & He & HJ3 & HP3 & Hfr3 & Hperm3 & HK3 & HMO3 & [HX3 HGK3]).
assert (Ee : e = 0) by (unfold SETTLE_EV in He; lia). subst e. rewrite Z.add_0_r in HJ3.
rewrite R1a.
(* the facts carried across settle *)
pose proof HJ3 as (_ & _ & (memS3 & HJi3 & _) & _). rewrite !Z.add_0_r in HJi3.
pose proof HJi3 as (HAR3 & Hly3 & _ & _ & _ & _ & Hnev3 & _).
clear HJi3 memS3.
assert (FA3 : forall cid pos, frame_addr ly3 cid pos = frame_addr lyc cid pos).
{ intros cid pos. unfold frame_addr.
  destruct Hly0 as (_ & _ & _ & _ & _ & EF0 & _). destruct Hly3 as (_ & _ & _ & _ & _ & EF3 & _).
  rewrite EF0, EF3. reflexivity. }
assert (ETOP3 : ly_top ly3 = ly_top lyc).
{ destruct Hly0 as (_ & _ & _ & _ & _ & _ & _ & _ & ET0 & _). destruct Hly3 as (_ & _ & _ & _ & _ & _ & _ & _ & ET3 & _).
  rewrite ET0, ET3. reflexivity. }
assert (HTOPc : ly_top lyc <= 2 ^ 47).
{ destruct Hly0 as (_ & _ & _ & _ & _ & _ & _ & _ & ET0 & _). rewrite ET0. lia. }
assert (KC2 : acall_kept_g segs B TG.G_HARNESS_B lyc Sc W memc W3 mem3 (spZ regs - RECV_STK) (spZ regs)
  (recv_wr bytes)).
{ apply (dk_kept_trans_nf_g segs B TG.G_HARNESS_B lyc Sc ly2 S2 W memc W2 (ms_mem ms1) W3 mem3
    (spZ regs - RECV_STK) (spZ regs) (spZ (ms_regs ms1) - SETTLE_STK) (spZ (ms_regs ms1)) (recv_wr bytes)
    (fun _ => False) (fun _ => False)
    HCE ltac:(lia) FA2 ltac:(intros f Hf; rewrite Hfr2; exact Hf) BL2
    (fun _ _ _ _ _ H => H) (fun _ _ _ _ _ H => H) KC1 HK3).
  - rewrite Hsp1, EST. lia.
  - rewrite Hsp1. lia.
  - intros x Hx. destruct Hx. }
assert (G2 : YK11.getr regs3 (Z_to_bv 5 2) = Z_to_bv 64 (spZ regs - 128))
  by (rewrite (HP3 2 ltac:(unfold acallee_saved; lia)); exact Q2).
assert (PA1 : aregs_preserved regs2 regs3) by exact (aregs_preserved_trans _ _ _ P1 HP3).
assert (KS3 : forall x, spZ regs - 48 <= x < spZ regs -> aview segs (w_H W3) mem3 x = aview segs (w_H W2) mem2 x).
{ intros x Hx. destruct HK3 as (K31 & _).
  etransitivity; [apply K31; [lia | rewrite Hsp1; lia] | apply KA1v]. }
assert (Hsaved3 : Forall (fun o : Z * Z => rdword (aview segs (w_H W3) mem3) (spZ regs - fst o) =
    Some (bv_unsigned (YK11.getr regs (Z_to_bv 5 (snd o))))) RECV_SAVED)
  by exact (rsb_saved_ext W2 W3 mem2 mem3 (spZ regs) regs Hsaved KS3).
assert (HTW3' : tw_at TMAP_B (aview segs (w_H W3) mem3) B3)
  by exact (tw_kept_GB _ _ B3 HTWc (gx_kept_rows segs TG.G_HARNESS_B W2 (ms_mem ms1) W3 mem3 HGK3)).
assert (MLE3 : mo_le MT Sc S3 (mo_malloc MT n + 0)) by exact (mle_station MT Sc S2 S3 _ _ MTL Hmo2 HMO3).
clear HK3 HGK3 KC1 HS SHOK1 HEI1 EE1 HTWc.

(* ---- run 2, +0x160 .. +0x164: a0 = a, the call of the free wrapper ---- *)
pose proof (@rsb_entry fx rc W3 regs3 regs mem3 9576 G2 ltac:(lia) ltac:(lia) Hsaved3) as HS.
set (E2 := rsb_E regs3 regs) in HS.
assert (HEI2 : img_env VAL A_LIM E2) by (unfold E2, rsb_E; apply Eimg_env).
assert (EE2 : forall n0 (r : bv 5), Z.of_nat n0 = bv_unsigned r -> ew E2 n0 = YK11.getr regs3 r)
  by (intros n0 r Hn0; unfold E2; apply rsb_ew_reg; exact Hn0).
assert (SHOK2 : sh_ok segs RSB_Bx RSB_SH E2 (mrestrict (w_H W3) mem3)) by (unfold sh_ok, RSB_SH; apply Forall_nil).
pose proof (rsb_KA_refl W3 mem3) as KA2.
paj_run_tok RUN HS HJ3 SHOK2 YC4b.Bspan.
{ rsb_awr. }
rsb_after KA2 HS.
lazymatch type of HS with context [restrict _ ?m] => rename m into ms2 end.
pmkst HS.
rsb_reg HS (1%bv : bv 5) (Z_to_bv 64 (BASE + 9584)) F1 ltac:(apply codeptr_val; exact HEI2).
rsb_reg HS (Z_to_bv 5 2) (Z_to_bv 64 (spZ regs - 128)) F2
  ltac:(cbn [sv_denot]; rewrite (EE2 2%nat (Z_to_bv 5 2) eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; exact G2).
rsb_reg HS (Z_to_bv 5 3) (YK11.getr regs (Z_to_bv 5 3)) F3 ltac:(rsb_keep EE2 PA1 3%nat 3 R3).
rsb_reg HS (Z_to_bv 5 4) (YK11.getr regs (Z_to_bv 5 4)) F4 ltac:(rsb_keep EE2 PA1 4%nat 4 R4).
rsb_reg HS (Z_to_bv 5 10) (Z_to_bv 64 a) F10 ltac:(rsb_keep EE2 PA1 8%nat 8 R8).
assert (P2 : aregs_preserved regs3 (ms_regs ms2))
  by (apply (aregs_preserved_of_st_ok segs (w_H W3) E2 _ ms2 regs3 (rsb_extra regs) HS);
      [ exact (rsb_agree regs3 regs) | vm_compute; reflexivity ]).
assert (SPF2 : spZ (ms_regs ms2) = spZ regs - 128).
{ change (bv_unsigned (YK11.getr (ms_regs ms2) (Z_to_bv 5 2)) = spZ regs - 128). rewrite F2.
  apply unsigned_lit_small. lia. }
destruct KA2 as [KA2v KA2p].
assert (KC3 : acall_kept_g segs B TG.G_HARNESS_B lyc Sc W memc W3 (ms_mem ms2) (spZ regs - RECV_STK) (spZ regs)
  (recv_wr bytes)).
{ apply (dk_kept_trans_g segs B TG.G_HARNESS_B lyc Sc W memc W3 mem3 W3 (ms_mem ms2) (spZ regs - RECV_STK)
    (spZ regs) (spZ regs) (spZ regs) (recv_wr bytes) (fun _ => False) HCE ltac:(lia) KC2
    (rsb_kept_g B TG.G_HARNESS_B lyc Sc W3 mem3 (ms_mem ms2) (spZ regs) _ (conj KA2v KA2p))
    ltac:(lia) ltac:(lia) (fun x Hx => False_ind _ Hx)). }
assert (HTWr : tw_at TMAP_B (aview segs (w_H W3) (ms_mem ms2)) B3)
  by exact (tw_kept TMAP_B _ _ B3 HTW3' (fun x _ => KA2v x)).
assert (Hsaved3b : Forall (fun o : Z * Z => rdword (aview segs (w_H W3) (ms_mem ms2)) (spZ regs - fst o) =
    Some (bv_unsigned (YK11.getr regs (Z_to_bv 5 (snd o))))) RECV_SAVED)
  by exact (rsb_saved_ext W3 W3 mem3 (ms_mem ms2) (spZ regs) regs Hsaved3 (fun x _ => KA2v x)).
(* the free's premises *)
assert (IN3 : In (a, n) (ablocks B ly3 S3))
  by (apply (Permutation_in _ (Permutation_sym (Permutation_trans Hperm3 Hperm2))); left; reflexivity).
destruct (al_blocks _ _ LAWS ly3 S3 W3 mem3 md3 a n HAR3 IN3) as (_ & _ & HceA & _ & _).
pose proof (req_size_pos n ltac:(lia)) as [Hrq _].
assert (S0b : YK11.getr (ms_regs ms2) (Z_to_bv 5 8) = Z_to_bv 64 a).
{ rewrite (P2 8 ltac:(unfold acallee_saved; lia)), (PA1 8 ltac:(unfold acallee_saved; lia)). exact R8. }
assert (ERAV : BASE + 9584 = RECV_RA_FREE) by (vm_compute; reflexivity).
assert (ERA : raZ (ms_regs ms2) = RECV_RA_FREE).
{ change (bv_unsigned (YK11.getr (ms_regs ms2) (1%bv : bv 5)) = RECV_RA_FREE).
  rewrite F1, <- ERAV. apply unsigned_lit_small. rewrite HBASE. lia. }
assert (HCH : chain_pre ly3 (aview segs (w_H W3) (ms_mem ms2)) (ms_regs ms2) []).
{ apply rsb_chain_nil.
  - rewrite ERA. unfold RECV_RA_FREE. vm_compute. discriminate.
  - change (bv_unsigned (YK11.getr (ms_regs ms2) (Z_to_bv 5 8)) <= spZ (ms_regs ms2)).
    rewrite S0b, SPF2, unsigned_lit_small by lia. lia. }
assert (HTR : In (call_trace0 (pc_free_ra0 (as_code B)) (ms_regs ms2) []) (as_universe B)).
{ rewrite AALLOC.gx_trace0. cbn [spine map flat_map]. rewrite ERA. exact Htrf. }
assert (HCOV : In (a, n) (ablocks B ly S) -> forall i, 0 <= i < req_size n -> inFP FP (a + i))
  by exact (AALLOC.gx_start_fp segs B TG.G_HARNESS_B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k a n HJ0
       FRESH).
assert (HMOK : mo_ok MT S3 (mo_free MT)).
{ apply (mok_station MT Sc S3 T (mo_malloc MT n + 0) (mo_free MT) MTL Hmo MLE3 (mo_free_nonneg MT MTL)). lia. }
lazymatch goal with |- SRr ?sg ?Wx (mkCfg (@YK11.mkst _ ?rg _ ?mm ?rom) ?mdx) ?Q =>
  change (SRr sg Wx (mkCfg (@YK11.mkst fx rg
    (Z_to_bv 64 (transportb_sigma TB___interceptor_trampoline_free)) mm rom) mdx) Q) end.
rewrite <- HFPC.
eapply SRr_bind.
{ exact (@AALLOC.gx_free_at fx rc tfib_sink_head segs B LAWS transportb_segs_low MT (AFREE fx) TG.G_HARNESS_B W3
    (ms_regs ms2) (ms_mem ms2) STK sp0 FP ly S W0 mem0 md0 own ly3 S3 _ (k + 1) a n (spZ regs - 128 - sp0)
    (Z_to_bv 64 (BASE + 9584)) []
    HJ3 IN3 F10 ltac:(rewrite SPF2; lia)
    ltac:(replace (spZ regs - 128 - sp0) with (spZ regs - sp0 + (-8) * 16) by lia;
          rewrite Z_mod_plus_full, Zminus_mod, Hsp16, Hsp0a; reflexivity)
    ltac:(lia) ltac:(rewrite EAS; rewrite EST in Hwlo; lia)
    (eq_trans F3 Hgp) (eq_trans F4 Htp) F1
    ltac:(apply (ret_ok_codeptr_v (PI := PI_transportb)); [lia | reflexivity])
    ltac:(rewrite EEV in Hnev; lia) HCH HTR HCOV HMOK). }
intros W4 c4 _ (ly4 & S4 & regs4 & mem4 & md5 & -> & HJ5 & HP5 & HBL5 & HFR5 & HK5 & HML5).
replace (sp0 + (spZ regs - 128 - sp0)) with (spZ regs - 128) in HK5 by lia.
pose proof (acall_kept_g_of segs B TG.G_HARNESS_B ly3 S3 W3 (ms_mem ms2) W4 mem4 _ _ _ HK5) as HK5g.
assert (KC4 : acall_kept_g segs B TG.G_HARNESS_B lyc Sc W memc W4 mem4 (spZ regs - RECV_STK) (spZ regs)
  (recv_wr bytes)).
{ apply (dk_kept_trans_nf_g segs B TG.G_HARNESS_B lyc Sc ly3 S3 W memc W3 (ms_mem ms2) W4 mem4
    (spZ regs - RECV_STK) (spZ regs) (spZ regs - 128 - ASTACK) (spZ regs - 128) (recv_wr bytes)
    (fun x => a <= x < a + req_size n) (fun x => a <= x < a + req_size n) HCE ltac:(lia) FA3
    ltac:(intros f Hf; rewrite Hfr3, Hfr2; exact Hf)
    ltac:(intros bm Hb; exact (Permutation_in _ (Permutation_sym Hperm3) (BL2 bm Hb)))
    NFB NFF KC3 HK5g).
  - rewrite EAS, EST. lia.
  - lia.
  - intros x Hx. right. exact Hx. }
assert (PERM4 : Permutation (ablocks B ly4 S4) (ablocks B lyc Sc)).
{ destruct HBL5 as (l1 & l2 & Eb1 & Eb2). rewrite Eb2.
  assert (HPx : Permutation (l1 ++ (a, n) :: l2) ((a, n) :: ablocks B lyc Sc))
    by (rewrite <- Eb1; exact (Permutation_trans Hperm3 Hperm2)).
  exact (ASET.rs_perm_rm _ _ _ _ HPx). }
assert (HTW4 : tw_at TMAP_B (aview segs (w_H W4) mem4) B3).
{ apply (tw_kept_GB _ _ B3 HTWr).
  exact (gx_kept_rows segs TG.G_HARNESS_B W3 (ms_mem ms2) W4 mem4
    (gx_kept_of_acall_kept segs B TG.G_HARNESS_B ly3 S3 W3 (ms_mem ms2) W4 mem4 _ _ _ HGX HGNE HK5)). }
pose proof (mle_station MT Sc S3 S4 _ _ MTL MLE3 HML5) as MLE4.
assert (KS4 : forall x, spZ regs - 48 <= x < spZ regs -> aview segs (w_H W4) mem4 x = aview segs (w_H W3) (ms_mem ms2) x).
{ intros x Hx. destruct HK5 as (K51 & _). apply K51; [lia | rewrite EAS; lia]. }
assert (Hsaved4 : Forall (fun o : Z * Z => rdword (aview segs (w_H W4) mem4) (spZ regs - fst o) =
    Some (bv_unsigned (YK11.getr regs (Z_to_bv 5 (snd o))))) RECV_SAVED)
  by exact (rsb_saved_ext W3 W4 (ms_mem ms2) mem4 (spZ regs) regs Hsaved3b KS4).
assert (G2' : YK11.getr regs4 (Z_to_bv 5 2) = Z_to_bv 64 (spZ regs - 128))
  by (rewrite (HP5 2 ltac:(unfold acallee_saved; lia)); exact F2).
assert (PA2 : aregs_preserved regs2 regs4)
  by exact (aregs_preserved_trans _ _ _ PA1 (aregs_preserved_trans _ _ _ P2 HP5)).
clear HK5 HK5g KC3 HS SHOK2 HEI2 EE2 HTWr.

(* ---- run 3, +0x168 .. +0x184: the six reloads, sp + 128, the return ---- *)
pose proof (@rsb_entry fx rc W4 regs4 regs mem4 9584 G2' ltac:(lia) ltac:(lia) Hsaved4) as HS.
set (E3 := rsb_E regs4 regs) in HS.
assert (HEI3 : img_env VAL A_LIM E3) by (unfold E3, rsb_E; apply Eimg_env).
assert (EE3 : forall n0 (r : bv 5), Z.of_nat n0 = bv_unsigned r -> ew E3 n0 = YK11.getr regs4 r)
  by (intros n0 r Hn0; unfold E3; apply rsb_ew_reg; exact Hn0).
destruct (rsb_ew_saved regs4 regs) as (X33 & X34 & X35 & X36 & X37 & X38).
fold E3 in X33, X34, X35, X36, X37, X38.
assert (SHOK3 : sh_ok segs RSB_Bx RSB_SH E3 (mrestrict (w_H W4) mem4)) by (unfold sh_ok, RSB_SH; apply Forall_nil).
pose proof (rsb_KA_refl W4 mem4) as KA3.
paj_run_tok RUN HS HJ5 SHOK3 YC4b.Bspan.
{ rsb_awr. }
rsb_after KA3 HS.
lazymatch type of HS with context [restrict _ ?m] => rename m into ms3 end.
rsb_reg HS (1%bv : bv 5) (YK11.getr regs (1%bv : bv 5)) V1 ltac:(rsb_sv X33).
rsb_reg HS (Z_to_bv 5 2) (YK11.getr regs (Z_to_bv 5 2)) V2
  ltac:(cbn [sv_denot]; rewrite (EE3 2%nat (Z_to_bv 5 2) eq_refl), G2';
        rewrite unsigned_lit_small by lia; replace (spZ regs - 128 + 128) with (spZ regs) by lia;
        unfold spZ; apply Z_to_bv_bv_unsigned).
rsb_reg HS (Z_to_bv 5 3) (YK11.getr regs (Z_to_bv 5 3)) V3 ltac:(rsb_keep EE3 PA2 3%nat 3 R3).
rsb_reg HS (Z_to_bv 5 4) (YK11.getr regs (Z_to_bv 5 4)) V4 ltac:(rsb_keep EE3 PA2 4%nat 4 R4).
rsb_reg HS (Z_to_bv 5 8) (YK11.getr regs (Z_to_bv 5 8)) V8 ltac:(rsb_sv X34).
rsb_reg HS (Z_to_bv 5 9) (YK11.getr regs (Z_to_bv 5 9)) V9 ltac:(rsb_sv X35).
rsb_reg HS (Z_to_bv 5 18) (YK11.getr regs (Z_to_bv 5 18)) V18 ltac:(rsb_sv X36).
rsb_reg HS (Z_to_bv 5 19) (YK11.getr regs (Z_to_bv 5 19)) V19 ltac:(rsb_sv X37).
rsb_reg HS (Z_to_bv 5 20) (YK11.getr regs (Z_to_bv 5 20)) V20 ltac:(rsb_sv X38).
rsb_reg HS (Z_to_bv 5 21) (YK11.getr regs (Z_to_bv 5 21)) V21 ltac:(rsb_keep EE3 PA2 21%nat 21 R21).
rsb_reg HS (Z_to_bv 5 22) (YK11.getr regs (Z_to_bv 5 22)) V22 ltac:(rsb_keep EE3 PA2 22%nat 22 R22).
rsb_reg HS (Z_to_bv 5 23) (YK11.getr regs (Z_to_bv 5 23)) V23 ltac:(rsb_keep EE3 PA2 23%nat 23 R23).
rsb_reg HS (Z_to_bv 5 24) (YK11.getr regs (Z_to_bv 5 24)) V24 ltac:(rsb_keep EE3 PA2 24%nat 24 R24).
rsb_reg HS (Z_to_bv 5 25) (YK11.getr regs (Z_to_bv 5 25)) V25 ltac:(rsb_keep EE3 PA2 25%nat 25 R25).
rsb_reg HS (Z_to_bv 5 26) (YK11.getr regs (Z_to_bv 5 26)) V26 ltac:(rsb_keep EE3 PA2 26%nat 26 R26).
rsb_reg HS (Z_to_bv 5 27) (YK11.getr regs (Z_to_bv 5 27)) V27 ltac:(rsb_keep EE3 PA2 27%nat 27 R27).
assert (HPT : aregs_preserved regs (ms_regs ms3)).
{ intros r Hr. unfold acallee_saved in Hr.
  assert (Hc : r = 2 \/ r = 3 \/ r = 4 \/ r = 8 \/ r = 9 \/ r = 18 \/ r = 19 \/ r = 20 \/ r = 21 \/ r = 22 \/
               r = 23 \/ r = 24 \/ r = 25 \/ r = 26 \/ r = 27) by lia.
  clear Hr.
  destruct Hc as [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | ->]]]]]]]]]]]]]];
    assumption. }
destruct KA3 as [KA3v KA3p].
assert (KC5 : acall_kept_g segs B TG.G_HARNESS_B lyc Sc W memc W4 (ms_mem ms3) (spZ regs - RECV_STK) (spZ regs)
  (recv_wr bytes)).
{ apply (dk_kept_trans_g segs B TG.G_HARNESS_B lyc Sc W memc W4 mem4 W4 (ms_mem ms3) (spZ regs - RECV_STK)
    (spZ regs) (spZ regs) (spZ regs) (recv_wr bytes) (fun _ => False) HCE ltac:(lia) KC4
    (rsb_kept_g B TG.G_HARNESS_B lyc Sc W4 mem4 (ms_mem ms3) (spZ regs) _ (conj KA3v KA3p))
    ltac:(lia) ltac:(lia) (fun x Hx => False_ind _ Hx)). }
assert (HTW5 : tw_at TMAP_B (aview segs (w_H W4) (ms_mem ms3)) B3)
  by exact (tw_kept TMAP_B _ _ B3 HTW4 (fun x _ => KA3v x)).
assert (Hpc : v_jalr (YK11.getr (ms_regs ms3) 1) 0 = YK11.getr regs 1) by (rewrite V1; exact Hret).
lazymatch goal with |- SRr _ _ (mkCfg _ ?mdx) _ => set (md6 := mdx) in * end.
clearbody md6.
lazymatch type of HS with st_ok_pi _ _ ?Ex ?ssx (restrict _ ?msx) =>
  eapply (paj_ret_at (fx := fx) (PL := PL_transportb) (PI := PI_transportb) W4 Ex ssx msx md6 _ HS eq_refl
    ltac:(clear; vm_compute; reflexivity)) end.
intros mat3.
(* the post: the return is receive's *)
unfold transport_recv_post, transport_cg_post.
exists ly4, S4, (ms_regs ms3), (ms_mem ms3). eexists. exists 2.
split; [rewrite Hpc; reflexivity|].
split; [unfold RECV_EV; lia|].
split; [replace (k + 2) with (k + 1 + 1) by lia;
        apply (ajournal_gx_materialize segs B LAWS transportb_segs_low); exact HJ5|].
split; [exact HPT|].
split; [rewrite HFR5, Hfr3; exact Hfr2|].
split; [exact PERM4|].
split; [exact KC5|].
split.
{ apply (mle_weaken MT Sc S4 _ _ MTL MLE4).
  change (recv_cost MT (Z.of_nat (length bytes))) with (mo_malloc MT n + mo_free MT). lia. }
exists a, Bw'. split; [exact Haddr|]. split; [exact Hrm|].
rewrite HX3. split; [exact HTW5 | exact HGF3].
Qed.

End s.
