(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: restates text of projects/cgif/cgif_file_fuzzer/proofs/lib/YCbq.v:528-543, 616-634;
   projects/cgif/cgif_rgb_fuzzer/proofs/lib/YC05.v:41-45, 208-214, 230-234, for libreac/fuzz_identity's asan-ubsan build
   (lib/B). The same text also appears in projects/cgif/cgif_file_fuzzer/proofs/lib/YCbo.v:420-423, 430-444, 447-448,
   453-455, 470-475, 477-486, 489-491, 502-505, 511-514, 1255-1258. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_identity/lib/B/Prog/reac_box_name_seg_rel.v, with its module paths, module names and numbers changed; 706 of its 765 lines of code are new or changed and 1865 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libdiginet/fuzz_transport/lib/A/Prog/on_announce_seg_tail.v, with its module names changed; 470 of its 536 lines of code are new or changed and 699 lines of the source are left out. *)
(* receive_seg_set: the last piece of the image-A walk of receive (lib/A/Prog/receive_seg_cut.v), Lemma recv_set :
   recv_set_stmt, from the set cut RECV_SET (+0x274, 0x83a44) to receive's return, which is the free wrapper's return.
   The code (offsets from AF_receive, listing lib/A/Prog/DgnTransportList.v):
     +0x274          `mv a0, s1`: a0 = ticked (s1 at the cut, recv_regs_set);
     +0x278          `jal settle` (return address +0x27c = 0x83a4c): settle_cg.v transport_settle_cg, a donor-form
                     callee lifted into the caller's G journal by TransportGCg.v gx_call_cg (G_HARNESS_gx_ok /
                     G_HARNESS_gx_noerrno, carried in recv_laws), from sp = the entry sp - 64, with tw_at at B3, settle_m
                     B3 ticked = Some (Bw', tt), invariant (2) of TRunInv.run_inv B3 and no event. Its X gives
                     Bw' = B3; its gx_kept carries the world relation (TWorldA.v tw_kept_GA); its acall_kept_g,
                     stated at its call state (the caller's blocks with the frame's block), folds into the cut's by
                     dk_kept_trans_nf_g with no own frame; its window lies below the seven saved words, which it keeps;
     +0x27c          `mv a0, s0`: a0 = a, the block the malloc returned;
     +0x280 .. +0x298  the seven reloads `ld ra, s0 .. s5` from the words the prologue saved (recv_cur's RECV_SAVED):
                     each register gets back its entry value;
     +0x29c          `addi sp, sp, 64`: sp = the entry sp;
     +0x2a0          `j` the free wrapper: receive_seg_alloc.v gx_free_at (YC5d.v afree04_rule in the G journal) at
                     pc_wrap_free (recv_laws), o = the entry sp - sp0, the entry ra, the entry chain (YCbq.v
                     achain_kept, achain_ly_top, achain_chain_pre: the chain's records lie at or above the entry sp, kept
                     by the walk's acall_kept_g), the trace of recv_fix (gx_trace0), the footprint premise by
                     gx_start_fp (the block is none of the caller's: the blocks are pairwise apart, sep_blocks_pos) and
                     the meter by mok_station.
   Both stretches of straight code are runs of the token engine over the G journal (TransportGRunA.v paj_run_x) from a
   symbolic state whose only region is the seven saved words (read only, rs_entry); each run stops at its call (the
   jal, the tail j) and writes no memory (rs_KA_step). The free's return is receive's: transport_recv_post with two
   events, the callee-saved registers the reloads' (and gp, tp, s6 .. s11 never written), the block removed from the
   blocks (Permutation), the free's acall_kept folded with dk_kept_trans_nf_g (its written range is the block, apart
   from the caller's blocks and frames: rs_blk_apart, rs_blk_frames), the meter charged the malloc, 0 and the free, and
   X at the malloc's address a: receive_m's Bw' (recv_res), the world relation at Bw' = B3 (G kept by settle and the
   free: gx_kept_of_acall_kept) and g_fail_next Bw' <= 1. *)
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
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import
DgnTransportSyms DgnTransportList DgnTransportAddr DgnTransportPa DgnTransportImg DgnTransportPaLib YC4b YC1g YC1h.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A Require Import AB1v Img0.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A Require AE2k AsanCells TransportG.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A Require Import W_journalG.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import DgnTransportCg TransportGCg TransportGRunA.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import TWorldG TWorldA TImgA.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import
settle_cg receive_cg receive_seg_cut receive_seg_alloc.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel Require TWorld TCb TImg TSess0 TSess TOps.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.
Module YK11 := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YK11.
Module TG := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.TransportG.
Module TW := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TWorld.
Module TC := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TCb.
Module TS0 := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TSess0.
#[global] Remove Hints OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5b.src0_sink_head
  OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5c.src0_sink
  OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5c.src0_sink_laws : typeclass_instances.

(* ------------------------------------------------------------------ *)
(* 1. The symbolic state of the two runs                               *)
(* ------------------------------------------------------------------ *)

(* Atoms: 0 .. 31 the registers at the run's start, 32 the shadow base (no shadow entry: no instrumented check on this
   code), 33 .. 39 the entry values of ra, s0, s1, s2, s3, s4, s5 (RECV_SAVED, in its order). The one region: the seven
   saved words at sp + 8 .. sp + 64 (sp = the entry sp - 64, atom 2), read only. *)
Definition rs_rg_sv : YP09.region :=
  YP09.mkRegion (Some 2%nat) 8 64 0 0
    [YP09.mkChunk 56 (CVal 8 (SOff 33 0)); YP09.mkChunk 48 (CVal 8 (SOff 34 0));
     YP09.mkChunk 40 (CVal 8 (SOff 35 0)); YP09.mkChunk 32 (CVal 8 (SOff 36 0));
     YP09.mkChunk 24 (CVal 8 (SOff 37 0)); YP09.mkChunk 16 (CVal 8 (SOff 38 0));
     YP09.mkChunk 8 (CVal 8 (SOff 39 0))].
Definition rs_regions : smem := [rs_rg_sv].
Definition rs_facts : facts := mkFacts [] [] [].
Definition ss_rs (pc : Z) : sstate := mkSS pc sr_atoms rs_regions None rs_facts.
Definition RS_SH : list shent := [].
Definition RS_Bx : sv := SOff 32 0.
(* The return address of the call of settle (+0x27c), where the second run starts. *)
Definition RS_RET : Z := AF_receive + 0x27c.
Lemma rs_ret_val : RS_RET = 10216.
Proof. reflexivity. Qed.

(* The values of atoms 32 .. 39. *)
Definition rs_extra (regs : bvmap 5 word) : list word :=
  Z_to_bv 64 SHADOW_OFF :: map (fun o : Z * Z => YK11.getr regs (Z_to_bv 5 (snd o))) RECV_SAVED.

(* The write rights of a run from a state with rs_regions: no region has a writable byte. *)
Ltac rs_awr :=
  lazymatch goal with |- awr_ok_x ?Ex ?rs ?Gx ?XO ?OUT ?stk ?sp0q ?fp ?b0 ?bc ?lyq ?ownq =>
    let rs' := eval vm_compute in rs in change (awr_ok_x Ex rs' Gx XO OUT stk sp0q fp b0 bc lyq ownq) end;
  repeat (apply awr_ok_x_cons;
    [ let a := fresh "a" in let Ha := fresh "Ha" in intros a Ha;
      cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha; lia |]);
  apply awr_ok_x_nil.

(* The value of register r in the machine state of HS: its symbolic value, computed, then tac. *)
Ltac rs_reg HS r v H tac :=
  lazymatch type of HS with
  | st_ok_pi ?segsx ?vl ?Ex ?ssx (restrict ?Hh ?msx) =>
      let e := eval vm_compute in (sr_get (ss_regs ssx) r) in
      assert (H : YK11.getr (ms_regs msx) r = v) by
        (refine (eq_trans (st_ok_pi_restrict_reg Hh Ex ssx msx r HS) _); change (sv_denot Ex e = v); tac)
  | OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YP0l.st_ok ?segsx ?Ex ?ssx (restrict ?Hh ?msx) =>
      let e := eval vm_compute in (sr_get (ss_regs ssx) r) in
      assert (H : YK11.getr (ms_regs msx) r = v) by
        (refine (eq_trans (st_ok_restrict_reg segsx Hh Ex ssx msx r HS) _); change (sv_denot Ex e = v); tac)
  | ?T => idtac "rs_reg: no match for" T; fail
  end.

(* A permutation of x :: rest lists x and a member y of rest at two places. *)
Lemma rs_perm_two : forall {X : Type} (l rest : list X) (x y : X),
  Permutation l (x :: rest) -> In y rest -> exists l1 l2 l3, l = l1 ++ x :: l2 ++ y :: l3 \/ l = l1 ++ y :: l2 ++ x :: l3.
Proof.
  intros X l rest x y HP Hin.
  assert (Hx : In x l) by (apply (Permutation_in _ (Permutation_sym HP)); left; reflexivity).
  apply in_split in Hx as (c & d & ->).
  assert (HP2 : Permutation rest (c ++ d)) by (eapply Permutation_cons_app_inv; apply Permutation_sym; exact HP).
  pose proof (Permutation_in _ HP2 Hin) as Hin2.
  apply in_app_or in Hin2 as [Hc | Hd].
  - apply in_split in Hc as (e & f & ->). exists e, f, d. right. rewrite <- app_assoc. reflexivity.
  - apply in_split in Hd as (e & f & ->). exists c, e, f. left. reflexivity.
Qed.

Lemma rs_perm_rm : forall {X : Type} (l1 l2 rest : list X) (x : X),
  Permutation (l1 ++ x :: l2) (x :: rest) -> Permutation (l1 ++ l2) rest.
Proof.
  intros X l1 l2 rest x H. apply Permutation_sym. eapply Permutation_cons_app_inv. apply Permutation_sym. exact H.
Qed.

Section e. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Local Abbreviation segs := tfibsegs.
Local Abbreviation VAL := (@pa_val _ transport_listing PI_transport).
Local Abbreviation BASE := (@pa_val _ transport_listing PI_transport A_TEXT).

Definition rs_E (regsX regs : bvmap 5 word) : env := Eimg (PI := PI_transport) (Ereg regsX (rs_extra regs)).

Lemma rs_ew_reg : forall regsX regs n (r : bv 5), Z.of_nat n = bv_unsigned r ->
  ew (rs_E regsX regs) n = YK11.getr regsX r.
Proof. intros regsX regs n r Hn. unfold rs_E. apply ew_Eimg_Ereg_nat. exact Hn. Qed.

Lemma rs_ew_saved : forall regsX regs,
  ew (rs_E regsX regs) 33 = YK11.getr regs (Z_to_bv 5 1) /\ ew (rs_E regsX regs) 34 = YK11.getr regs (Z_to_bv 5 8) /\
  ew (rs_E regsX regs) 35 = YK11.getr regs (Z_to_bv 5 9) /\ ew (rs_E regsX regs) 36 = YK11.getr regs (Z_to_bv 5 18) /\
  ew (rs_E regsX regs) 37 = YK11.getr regs (Z_to_bv 5 19) /\ ew (rs_E regsX regs) 38 = YK11.getr regs (Z_to_bv 5 20) /\
  ew (rs_E regsX regs) 39 = YK11.getr regs (Z_to_bv 5 21).
Proof.
  intros regsX regs.
  assert (EX : forall j, (j < 8)%nat -> ew (rs_E regsX regs) (32 + j) = nth j (rs_extra regs) (Z_to_bv 64 0))
    by (intros j Hj; unfold rs_E; rewrite Eimg_low by (unfold A_TEXT; lia); apply ew_Ereg_extra).
  pose proof (EX 1%nat ltac:(lia)) as E1. pose proof (EX 2%nat ltac:(lia)) as E2.
  pose proof (EX 3%nat ltac:(lia)) as E3. pose proof (EX 4%nat ltac:(lia)) as E4.
  pose proof (EX 5%nat ltac:(lia)) as E5. pose proof (EX 6%nat ltac:(lia)) as E6.
  pose proof (EX 7%nat ltac:(lia)) as E7.
  cbn [Nat.add nth rs_extra map RECV_SAVED snd] in E1, E2, E3, E4, E5, E6, E7.
  repeat split; assumption.
Qed.

Lemma rs_agree : forall regsX regs, env_agree 32 (Ereg regsX (rs_extra regs)) (rs_E regsX regs).
Proof. intros regsX regs. split; [intros n Hn; unfold rs_E; apply Eimg_low; unfold A_TEXT; lia | reflexivity]. Qed.

(* A saved word read back as the chunk of its atom. *)
Lemma rs_chunk : forall E (H : word -> bool) (mem : word -> option byte) (b off : Z) (n : nat) (x : word),
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

(* The symbolic state at pc (the cut +0x274, or +0x27c after settle) holds of the machine state there: sp is the entry
   sp - 64 and the seven saved words hold the entry registers. *)
Lemma rs_entry : forall (W : world segs) (regsX regs : bvmap 5 word) mem pc,
  YK11.getr regsX (Z_to_bv 5 2) = Z_to_bv 64 (spZ regs - 64) ->
  YM05.alloc_ceiling <= spZ regs - 64 -> spZ regs <= 2 ^ 47 ->
  Forall (fun o : Z * Z => rdword (aview segs (w_H W) mem) (spZ regs - fst o) =
      Some (bv_unsigned (YK11.getr regs (Z_to_bv 5 (snd o))))) RECV_SAVED ->
  st_ok_pi segs VAL (rs_E regsX regs) (ss_rs pc)
    (restrict (w_H W) (@YK11.mkst fx regsX (Z_to_bv 64 (BASE + pc)) mem (YK11.seg_rom segs))).
Proof.
  intros W regsX regs mem pc R2 Hce H47 Hsaved.
  pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
  set (E := rs_E regsX regs).
  assert (U2 : bv_unsigned (ew E 2) = spZ regs - 64).
  { unfold E. rewrite (rs_ew_reg regsX regs 2 (Z_to_bv 5 2) eq_refl), R2. apply unsigned_lit_small. lia. }
  destruct (rs_ew_saved regsX regs) as (X33 & X34 & X35 & X36 & X37 & X38 & X39).
  fold E in X33, X34, X35, X36, X37, X38, X39.
  unfold RECV_SAVED in Hsaved.
  apply Forall_cons_iff in Hsaved as [Sra Hsaved]. apply Forall_cons_iff in Hsaved as [Ss0 Hsaved].
  apply Forall_cons_iff in Hsaved as [Ss1 Hsaved]. apply Forall_cons_iff in Hsaved as [Ss2 Hsaved].
  apply Forall_cons_iff in Hsaved as [Ss3 Hsaved]. apply Forall_cons_iff in Hsaved as [Ss4 Hsaved].
  apply Forall_cons_iff in Hsaved as [Ss5 _].
  cbn [fst snd] in Sra, Ss0, Ss1, Ss2, Ss3, Ss4, Ss5.
  rewrite restrict_mkst_fx. unfold ss_rs.
  apply (@pa_entry_st_ok_full fx rc transport_listing PI_transport).
  - apply regs_ok_Eimg_Ereg.
  - vm_compute. reflexivity.
  - apply Forall_cons; [|apply Forall_nil]. unfold rs_rg_sv, region_ok.
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val]. rewrite U2.
    split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
    apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons;
      [|apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]]]]]]].
    + apply (rs_chunk E (w_H W) mem (spZ regs - 64) 56 33 _ X33).
      replace (spZ regs - 64 + 56) with (spZ regs - 8) by lia. exact Sra.
    + apply (rs_chunk E (w_H W) mem (spZ regs - 64) 48 34 _ X34).
      replace (spZ regs - 64 + 48) with (spZ regs - 16) by lia. exact Ss0.
    + apply (rs_chunk E (w_H W) mem (spZ regs - 64) 40 35 _ X35).
      replace (spZ regs - 64 + 40) with (spZ regs - 24) by lia. exact Ss1.
    + apply (rs_chunk E (w_H W) mem (spZ regs - 64) 32 36 _ X36).
      replace (spZ regs - 64 + 32) with (spZ regs - 32) by lia. exact Ss2.
    + apply (rs_chunk E (w_H W) mem (spZ regs - 64) 24 37 _ X37).
      replace (spZ regs - 64 + 24) with (spZ regs - 40) by lia. exact Ss3.
    + apply (rs_chunk E (w_H W) mem (spZ regs - 64) 16 38 _ X38).
      replace (spZ regs - 64 + 16) with (spZ regs - 48) by lia. exact Ss4.
    + apply (rs_chunk E (w_H W) mem (spZ regs - 64) 8 39 _ X39).
      replace (spZ regs - 64 + 8) with (spZ regs - 56) by lia. exact Ss5.
  - cbn [pairwise_disjoint all_disjoint rs_regions]. split; exact I.
  - unfold rs_facts, facts_ok. cbn [f_atoms f_conds f_alias atoms_ok conds_ok alias_ok].
    repeat match goal with |- _ /\ _ => split end; exact I.
Qed.

(* What a run keeps, from its start memory m0 to a memory m: every byte's view, and presence. *)
Definition rs_KA (W : world segs) (m0 m : word -> option byte) : Prop :=
  (forall a, aview segs (w_H W) m a = aview segs (w_H W) m0 a) /\
  (forall a, apresent (w_H W) m0 a -> apresent (w_H W) m a).

Lemma rs_KA_refl : forall (W : world segs) m, rs_KA W m m.
Proof. intros W m. split; [intros a; reflexivity | intros a Ha; exact Ha]. Qed.

(* A run from a state with rs_regions writes nothing. *)
Lemma rs_KA_step : forall E (W : world segs) m0 (m m' : word -> option byte),
  rs_KA W m0 m ->
  frame_of E rs_regions (mrestrict (w_H W) m) (mrestrict (w_H W) m') ->
  mem_grows (mrestrict (w_H W) m) (mrestrict (w_H W) m') ->
  rs_KA W m0 m'.
Proof.
  intros E W m0 m m' [K1 K2] Hfr Hg. split.
  - assert (Hw : forall b wlo whi x, In (b, wlo, whi) (windows rs_regions) ->
      base_val E b + wlo <= x < base_val E b + whi -> (fun _ : Z => False) x).
    { intros b wlo whi x Hin Hx.
      lazymatch type of Hin with In ?y ?l => let l' := eval vm_compute in l in change (In y l') in Hin end.
      cbn [In] in Hin.
      repeat (destruct Hin as [Hin | Hin]; [injection Hin as <- <- <-; exfalso; lia |]).
      destruct Hin. }
    intros a.
    rewrite (aview_wrap64 segs (w_H W) m' a), (aview_wrap64 segs (w_H W) m0 a).
    rewrite (kept_of_frame E rs_regions (w_H W) m m' (fun _ => False) Hfr Hw (a mod 2 ^ 64)
      ltac:(apply Z.mod_pos_bound; lia) (fun x => x)).
    exact (K1 (a mod 2 ^ 64)).
  - intros a Ha. exact (apresent_grows _ _ _ a Hg (K2 a Ha)).
Qed.

Variable B : asyms.

(* What a run kept, as an acall_kept_g with an empty window. *)
Lemma rs_kept_g : forall G ly S (W : world segs) m0 m s (Eo : Z -> Prop),
  rs_KA W m0 m -> acall_kept_g segs B G ly S W m0 W m s s Eo.
Proof.
  intros G ly S W m0 m s Eo [K1 K2]. unfold acall_kept_g.
  split; [intros; apply K1|]. split; [intros; apply K1|]. split; [intros; apply K1|].
  split; [intros; apply K1|]. split; [intros a _ _ Ha; exact (K2 a Ha)|]. intros a Ha. lia.
Qed.

Hypothesis LAWS : AR_laws segs B.

(* A block listed first in a permutation of the live blocks is apart from every other listed block. *)
Lemma rs_blk_apart : forall ly S (W : world segs) m md (p nb : Z) rest b mm i,
  AR segs B ly S W m md -> Permutation (ablocks B ly S) ((p, nb) :: rest) -> In (b, mm) rest ->
  0 <= i < req_size mm -> p <= b + i < p + req_size nb -> False.
Proof.
  intros ly S W m md p nb rest b mm i HAR HP Hin Hi Hx.
  destruct (rs_perm_two _ _ _ _ HP Hin) as (l1 & l2 & l3 & [E | E]);
    pose proof (sep_blocks_pos segs B LAWS ly S W m md _ _ l1 l2 l3 HAR E) as D;
    unfold zdisjoint, block_rng in D; cbn [fst snd] in D; lia.
Qed.

(* A live block is apart from the live side-stack frames and their shadow bytes. *)
Lemma rs_blk_frames : forall ly2 S2 (W2 : world segs) m2 md2 lyc Sc p nb,
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
Ltac rs_after KA HS :=
  lazymatch goal with |- SRr _ _ (mkCfg _ (with_vm_backing (m_vm_lazy ?m0) ?mt ?m0)) _ =>
    let md := fresh "mdw" in set (md := with_vm_backing (m_vm_lazy m0) mt m0) in *; clearbody md; clear mt end;
  lazymatch goal with HFr : frame_of _ _ (mrestrict _ _) (mrestrict _ _), HG : mem_grows _ _ |- _ =>
    let KA' := fresh "KAn" in
    pose proof (rs_KA_step _ _ _ _ _ KA HFr HG) as KA'; clear KA HFr HG; rename KA' into KA end;
  lazymatch goal with HF : frame_of _ _ _ _ |- _ => clear HF end.

(* A register the walk keeps (gp, tp, s6 .. s11, or s0 into a0): its atom at the second run's start, through settle's
   aregs_preserved HP and the first run's P, to the cut's value Rr. *)
Ltac rs_keep EE HP P rn rz Rr :=
  cbn [sv_denot]; rewrite (EE rn (Z_to_bv 5 rz) eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned;
  rewrite (HP rz ltac:(unfold acallee_saved; lia)), (P rz ltac:(unfold acallee_saved; lia)); exact Rr.
(* A register reloaded from a saved word: the atom X of the word. *)
Ltac rs_sv X := cbn [sv_denot]; rewrite X, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity.

(* ------------------------------------------------------------------ *)
(* 2. The piece                                                        *)
(* ------------------------------------------------------------------ *)

Section s. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Local Abbreviation tfib_sink_head := AE2k.tfib_sink_head.
Variable B : asyms.
Variable MT : ameter_ops.
Local Abbreviation segs := tfibsegs.
Local Abbreviation VAL := (@pa_val _ transport_listing PI_transport).
Local Abbreviation BASE := (@pa_val _ transport_listing PI_transport A_TEXT).

Lemma recv_set : @recv_set_stmt fx rc B MT.
Proof.
unfold recv_set_stmt, recv_set_at.
intros LAWS0 CALLS STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs p by_poll pf T bytes Bw ch a Bw'
  ly2 S2 W2 mem2 md2 regs2 B3 ticked HFIX HCUR HRES HTW3 HGF3 HINV3 HSET Htk HREGS.
destruct LAWS0 as (HMPC & HFPC & HCELLS & HRC & HGU & HGE & HRU & HRE & LAWS & MTL & HGX & HGNE).
destruct CALLS as (_ & _ & _ & _ & _ & _ & SETC & AFREE).
destruct HFIX as (HJ0 & Hret & Hra4 & Hgp & Htp & _ & _ & _ & _ & Hch & Hsp16 & Hwlo & Hwhi & _ & _ & Hn &
  _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hnev & _ & Hmo & Hcost & _ & Htrf).
destruct HCUR as (HJ2 & Hfr2 & Hperm2 & Hmo2 & HK2 & Hsaved & Ha4096).
destruct HRES as (Haddr & Hrm).
destruct HREGS as ((R2 & R3 & R4 & R22 & R23 & R24 & R25 & R26 & R27) & R8 & R9).
destruct HINV3 as (_ & HQ3 & _).
set (n := Z.max 1 (Z.of_nat (length bytes))) in *.
assert (HC' : mo_malloc MT n + mo_free MT <= T) by exact Hcost.
clear Hcost.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (EST : RECV_STK = 16448) by reflexivity.
assert (ESS : SETTLE_STK = 8288) by reflexivity.
assert (EAS : ASTACK = 16384) by reflexivity.
assert (EEV : RECV_EV = 2) by reflexivity.
assert (HBASE : BASE = 0x81264) by (vm_compute; reflexivity).
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
assert (HSPB : YM05.alloc_ceiling + 16448 <= spZ regs <= 2 ^ 47) by (rewrite EST in Hwlo; lia).
assert (HCE : YM05.alloc_ceiling <= spZ regs - RECV_STK) by (rewrite EST; lia).
assert (Hn1 : 1 <= n) by (unfold n; lia).
(* the block, apart from the caller's blocks and frames, none of the caller's blocks *)
assert (INA2 : In (a, n) (ablocks B ly2 S2)) by (apply (Permutation_in _ (Permutation_sym Hperm2)); left; reflexivity).
assert (BL2 : forall bm, In bm (ablocks B lyc Sc) -> In bm (ablocks B ly2 S2))
  by (intros bm Hb; apply (Permutation_in _ (Permutation_sym Hperm2)); right; exact Hb).
assert (NFB : forall b m i, In (b, m) (ablocks B lyc Sc) -> 0 <= i < req_size m -> a <= b + i < a + req_size n -> False)
  by (intros b m i Hb Hi Hx; exact (rs_blk_apart B LAWS ly2 S2 W2 mem2 md2 a n _ b m i HAR2 Hperm2 Hb Hi Hx)).
assert (NFF : forall cid pos x, In (cid, pos) (frames Sc) ->
    (in_zr x (frame_rng lyc (cid, pos)) \/ in_zr x (shadow_addr (frame_addr lyc cid pos), fs_frame_bytes cid / 8)) ->
    a <= x < a + req_size n -> False)
  by exact (rs_blk_frames B LAWS ly2 S2 W2 mem2 md2 lyc Sc a n HAR2 INA2 Hfr2 FA2).
assert (FRESH : ~ In (a, n) (ablocks B lyc Sc)).
{ intros Hin. pose proof (req_size_pos n ltac:(lia)) as [Hr _].
  exact (NFB a n 0 Hin ltac:(lia) ltac:(lia)). }

(* +0x274 .. +0x278: a0 = ticked, the call of settle *)
pose proof (@rs_entry fx rc W2 regs2 regs mem2 RECV_SET ltac:(exact R2) ltac:(lia) ltac:(lia) Hsaved) as HS.
set (E1 := rs_E regs2 regs) in HS.
assert (HEI1 : img_env VAL A_LIM E1) by (unfold E1, rs_E; apply Eimg_env).
assert (EE1 : forall n0 (r : bv 5), Z.of_nat n0 = bv_unsigned r -> ew E1 n0 = YK11.getr regs2 r)
  by (intros n0 r Hn0; unfold E1; apply rs_ew_reg; exact Hn0).
assert (SHOK1 : sh_ok segs RS_Bx RS_SH E1 (mrestrict (w_H W2) mem2)) by (unfold sh_ok, RS_SH; apply Forall_nil).
pose proof (rs_KA_refl W2 mem2) as KA1.
pose proof (@paj_run_x fx rc tfib_sink_head transport_listing PL_transport PI_transport B LAWS TG.G_HARNESS HGX 0 [])
  as RUN.
paj_run_tok RUN HS HJ2 SHOK1 YC4b.Bspan.
{ rs_awr. }
rs_after KA1 HS.
lazymatch type of HS with context [restrict _ ?m] => rename m into ms1 end.
pmkst HS.
rs_reg HS (1%bv : bv 5) (Z_to_bv 64 (BASE + 10216)) R1a ltac:(apply codeptr_val; exact HEI1).
rs_reg HS (Z_to_bv 5 2) (Z_to_bv 64 (spZ regs - 64)) Q2
  ltac:(cbn [sv_denot]; rewrite (EE1 2%nat (Z_to_bv 5 2) eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; exact R2).
rs_reg HS (Z_to_bv 5 3) (YK11.getr regs (Z_to_bv 5 3)) Q3
  ltac:(cbn [sv_denot]; rewrite (EE1 3%nat (Z_to_bv 5 3) eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; exact R3).
rs_reg HS (Z_to_bv 5 4) (YK11.getr regs (Z_to_bv 5 4)) Q4
  ltac:(cbn [sv_denot]; rewrite (EE1 4%nat (Z_to_bv 5 4) eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; exact R4).
rs_reg HS (Z_to_bv 5 10) (Z_to_bv 64 ticked) Q10
  ltac:(cbn [sv_denot]; rewrite (EE1 9%nat (Z_to_bv 5 9) eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; exact R9).
assert (P1 : aregs_preserved regs2 (ms_regs ms1))
  by (apply (aregs_preserved_of_st_ok segs (w_H W2) E1 _ ms1 regs2 (rs_extra regs) HS);
      [ exact (rs_agree regs2 regs) | vm_compute; reflexivity ]).
assert (Hsp1 : spZ (ms_regs ms1) = spZ regs - 64).
{ change (bv_unsigned (YK11.getr (ms_regs ms1) (Z_to_bv 5 2)) = spZ regs - 64). rewrite Q2.
  apply unsigned_lit_small. lia. }
destruct KA1 as [KA1v KA1p].
assert (HTWc : tw_at TMAP_A (aview segs (w_H W2) (ms_mem ms1)) B3)
  by exact (tw_kept TMAP_A _ _ B3 HTW3 (fun x _ => KA1v x)).
assert (KC1 : acall_kept_g segs B TG.G_HARNESS lyc Sc W memc W2 (ms_mem ms1) (spZ regs - RECV_STK) (spZ regs)
  (recv_wr bytes)).
{ apply (dk_kept_trans_g segs B TG.G_HARNESS lyc Sc W memc W2 mem2 W2 (ms_mem ms1) (spZ regs - RECV_STK) (spZ regs)
    (spZ regs) (spZ regs) (recv_wr bytes) (fun _ => False) HCE ltac:(lia) HK2
    (rs_kept_g B TG.G_HARNESS lyc Sc W2 mem2 (ms_mem ms1) (spZ regs) _ (conj KA1v KA1p))
    ltac:(lia) ltac:(lia) (fun x Hx => False_ind _ Hx)). }
lazymatch goal with |- SRr ?sg ?Wx (mkCfg (@YK11.mkst _ ?rg _ ?mm ?rom) ?mdx) ?Q =>
  change (SRr sg Wx (@cfg_at fx segs (transport_sigma TS_settle) rg mm mdx) Q) end.
eapply SRr_bind.
{ apply (@gx_call_cg fx rc tfib_sink_head segs B MT TG.G_HARNESS STK sp0 FP ly S W0 mem0 md0 own ly2 S2 W2
    (ms_mem ms1) _ (k + 1) _ (ms_regs ms1) SETTLE_STK SETTLE_EV 0 (fun _ => False)
    (fun _ _ _ => Bw' = B3) HGX HGNE HJ2).
  intros memS HJS. eapply SRr_mono.
  { apply (SETC fx STK sp0 FP ly S W0 memS md0 own ly2 S2 W2 (ms_mem ms1) _ (k + 1) (ms_regs ms1) ticked B3 Bw' HJS).
    - rewrite R1a. apply (ret_ok_codeptr_v (PI := PI_transport)); [lia | reflexivity].
    - change (4096 <= bv_unsigned (YK11.getr (ms_regs ms1) 1%bv)). rewrite R1a, HBASE.
      rewrite unsigned_lit_small by lia. lia.
    - exact (eq_trans Q3 Hgp).
    - exact (eq_trans Q4 Htp).
    - exact Q10.
    - lia.
    - rewrite Hsp1. replace (spZ regs - 64) with (spZ regs + (-4) * 16) by lia. rewrite Z_mod_plus_full.
      exact Hsp16.
    - rewrite Hsp1, ESS. rewrite EST in Hwlo. lia.
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
assert (KC2 : acall_kept_g segs B TG.G_HARNESS lyc Sc W memc W3 mem3 (spZ regs - RECV_STK) (spZ regs) (recv_wr bytes)).
{ apply (dk_kept_trans_nf_g segs B TG.G_HARNESS lyc Sc ly2 S2 W memc W2 (ms_mem ms1) W3 mem3 (spZ regs - RECV_STK)
    (spZ regs) (spZ (ms_regs ms1) - SETTLE_STK) (spZ (ms_regs ms1)) (recv_wr bytes) (fun _ => False) (fun _ => False)
    HCE ltac:(lia) FA2 ltac:(intros f Hf; rewrite Hfr2; exact Hf) BL2
    (fun _ _ _ _ _ H => H) (fun _ _ _ _ _ H => H) KC1 HK3).
  - rewrite Hsp1, ESS, EST. lia.
  - rewrite Hsp1. lia.
  - intros x Hx. destruct Hx. }
assert (G2 : YK11.getr regs3 (Z_to_bv 5 2) = Z_to_bv 64 (spZ regs - 64))
  by (rewrite (HP3 2 ltac:(unfold acallee_saved; lia)); exact Q2).
assert (KS3 : forall x, spZ regs - 56 <= x < spZ regs -> aview segs (w_H W3) mem3 x = aview segs (w_H W2) mem2 x).
{ intros x Hx. destruct HK3 as (K31 & _).
  etransitivity; [apply K31; [lia | rewrite Hsp1, ESS; lia] | apply KA1v]. }
assert (Hsaved3 : Forall (fun o : Z * Z => rdword (aview segs (w_H W3) mem3) (spZ regs - fst o) =
    Some (bv_unsigned (YK11.getr regs (Z_to_bv 5 (snd o))))) RECV_SAVED).
{ assert (HSB : Forall (fun o : Z * Z => 8 <= fst o <= 56) RECV_SAVED)
    by (unfold RECV_SAVED; repeat apply Forall_cons; try apply Forall_nil; cbn [fst]; lia).
  apply Forall_forall. intros o Hoin. cbv beta.
  pose proof (proj1 (Forall_forall _ _) Hsaved o Hoin) as Ho.
  pose proof (proj1 (Forall_forall _ _) HSB o Hoin) as Hb.
  cbn beta in Ho, Hb.
  rewrite (rdword_ext (aview segs (w_H W2) mem2) (aview segs (w_H W3) mem3) (spZ regs - fst o)); [exact Ho|].
  intros k0 Hk0. apply KS3. lia. }
assert (HTW3' : tw_at TMAP_A (aview segs (w_H W3) mem3) B3)
  by exact (tw_kept_GA _ _ B3 HTWc (gx_kept_rows segs TG.G_HARNESS W2 (ms_mem ms1) W3 mem3 HGK3)).
assert (MLE3 : mo_le MT Sc S3 (mo_malloc MT n + 0)) by exact (mle_station MT Sc S2 S3 _ _ MTL Hmo2 HMO3).
clear HK3 HGK3 KC1 HS SHOK1 HEI1 EE1 HTWc.

(* +0x27c .. +0x2a0: a0 = a, the seven reloads, sp + 64, the tail jump to the free wrapper *)
pose proof (@rs_entry fx rc W3 regs3 regs mem3 10216 G2 ltac:(lia) ltac:(lia) Hsaved3) as HS.
set (E2 := rs_E regs3 regs) in HS.
assert (HEI2 : img_env VAL A_LIM E2) by (unfold E2, rs_E; apply Eimg_env).
assert (EE2 : forall n0 (r : bv 5), Z.of_nat n0 = bv_unsigned r -> ew E2 n0 = YK11.getr regs3 r)
  by (intros n0 r Hn0; unfold E2; apply rs_ew_reg; exact Hn0).
destruct (rs_ew_saved regs3 regs) as (X33 & X34 & X35 & X36 & X37 & X38 & X39).
fold E2 in X33, X34, X35, X36, X37, X38, X39.
assert (SHOK2 : sh_ok segs RS_Bx RS_SH E2 (mrestrict (w_H W3) mem3)) by (unfold sh_ok, RS_SH; apply Forall_nil).
pose proof (rs_KA_refl W3 mem3) as KA2.
paj_run_tok RUN HS HJ3 SHOK2 YC4b.Bspan.
{ rs_awr. }
rs_after KA2 HS.
lazymatch type of HS with context [restrict _ ?m] => rename m into ms2 end.
pmkst HS.
rs_reg HS (Z_to_bv 5 1) (YK11.getr regs (Z_to_bv 5 1)) F1 ltac:(rs_sv X33).
rs_reg HS (Z_to_bv 5 2) (YK11.getr regs (Z_to_bv 5 2)) F2
  ltac:(cbn [sv_denot]; rewrite (EE2 2%nat (Z_to_bv 5 2) eq_refl), G2;
        rewrite unsigned_lit_small by lia; replace (spZ regs - 64 + 64) with (spZ regs) by lia;
        unfold spZ; apply Z_to_bv_bv_unsigned).
rs_reg HS (Z_to_bv 5 3) (YK11.getr regs (Z_to_bv 5 3)) F3 ltac:(rs_keep EE2 HP3 P1 3%nat 3 R3).
rs_reg HS (Z_to_bv 5 4) (YK11.getr regs (Z_to_bv 5 4)) F4 ltac:(rs_keep EE2 HP3 P1 4%nat 4 R4).
rs_reg HS (Z_to_bv 5 8) (YK11.getr regs (Z_to_bv 5 8)) F8 ltac:(rs_sv X34).
rs_reg HS (Z_to_bv 5 9) (YK11.getr regs (Z_to_bv 5 9)) F9 ltac:(rs_sv X35).
rs_reg HS (Z_to_bv 5 18) (YK11.getr regs (Z_to_bv 5 18)) F18 ltac:(rs_sv X36).
rs_reg HS (Z_to_bv 5 19) (YK11.getr regs (Z_to_bv 5 19)) F19 ltac:(rs_sv X37).
rs_reg HS (Z_to_bv 5 20) (YK11.getr regs (Z_to_bv 5 20)) F20 ltac:(rs_sv X38).
rs_reg HS (Z_to_bv 5 21) (YK11.getr regs (Z_to_bv 5 21)) F21 ltac:(rs_sv X39).
rs_reg HS (Z_to_bv 5 22) (YK11.getr regs (Z_to_bv 5 22)) F22 ltac:(rs_keep EE2 HP3 P1 22%nat 22 R22).
rs_reg HS (Z_to_bv 5 23) (YK11.getr regs (Z_to_bv 5 23)) F23 ltac:(rs_keep EE2 HP3 P1 23%nat 23 R23).
rs_reg HS (Z_to_bv 5 24) (YK11.getr regs (Z_to_bv 5 24)) F24 ltac:(rs_keep EE2 HP3 P1 24%nat 24 R24).
rs_reg HS (Z_to_bv 5 25) (YK11.getr regs (Z_to_bv 5 25)) F25 ltac:(rs_keep EE2 HP3 P1 25%nat 25 R25).
rs_reg HS (Z_to_bv 5 26) (YK11.getr regs (Z_to_bv 5 26)) F26 ltac:(rs_keep EE2 HP3 P1 26%nat 26 R26).
rs_reg HS (Z_to_bv 5 27) (YK11.getr regs (Z_to_bv 5 27)) F27 ltac:(rs_keep EE2 HP3 P1 27%nat 27 R27).
rs_reg HS (Z_to_bv 5 10) (Z_to_bv 64 a) F10 ltac:(rs_keep EE2 HP3 P1 8%nat 8 R8).
assert (HPT : aregs_preserved regs (ms_regs ms2)).
{ intros r Hr. unfold acallee_saved in Hr.
  assert (Hc : r = 2 \/ r = 3 \/ r = 4 \/ r = 8 \/ r = 9 \/ r = 18 \/ r = 19 \/ r = 20 \/ r = 21 \/ r = 22 \/
               r = 23 \/ r = 24 \/ r = 25 \/ r = 26 \/ r = 27) by lia.
  clear Hr.
  destruct Hc as [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | ->]]]]]]]]]]]]]];
    assumption. }
assert (SPF : spZ (ms_regs ms2) = spZ regs) by exact (f_equal (@bv_unsigned 64) F2).
destruct KA2 as [KA2v KA2p].
assert (KC3 : acall_kept_g segs B TG.G_HARNESS lyc Sc W memc W3 (ms_mem ms2) (spZ regs - RECV_STK) (spZ regs)
  (recv_wr bytes)).
{ apply (dk_kept_trans_g segs B TG.G_HARNESS lyc Sc W memc W3 mem3 W3 (ms_mem ms2) (spZ regs - RECV_STK) (spZ regs)
    (spZ regs) (spZ regs) (recv_wr bytes) (fun _ => False) HCE ltac:(lia) KC2
    (rs_kept_g B TG.G_HARNESS lyc Sc W3 mem3 (ms_mem ms2) (spZ regs) _ (conj KA2v KA2p))
    ltac:(lia) ltac:(lia) (fun x Hx => False_ind _ Hx)). }
assert (HTWr : tw_at TMAP_A (aview segs (w_H W3) (ms_mem ms2)) B3)
  by exact (tw_kept TMAP_A _ _ B3 HTW3' (fun x _ => KA2v x)).
(* the free's premises *)
assert (IN3 : In (a, n) (ablocks B ly3 S3))
  by (apply (Permutation_in _ (Permutation_sym (Permutation_trans Hperm3 Hperm2))); left; reflexivity).
assert (HCH : chain_pre ly3 (aview segs (w_H W3) (ms_mem ms2)) (ms_regs ms2) ch).
{ apply (achain_chain_pre ly3 _ (spZ regs) (s0Z regs) ch (ms_regs ms2)).
  - apply (achain_ly_top lyc ly3 _ _ _ _ ETOP3).
    apply (achain_kept lyc (aview segs (w_H W) memc) _ (spZ regs) (s0Z regs) ch (spZ regs) Hch); [lia | lia |].
    intros x Hx. destruct KC3 as (K1 & _). apply K1; lia.
  - rewrite SPF. lia.
  - change (bv_unsigned (YK11.getr (ms_regs ms2) (Z_to_bv 5 8)) = bv_unsigned (YK11.getr regs (Z_to_bv 5 8))).
    rewrite F8. reflexivity.
  - change (4096 <= bv_unsigned (YK11.getr (ms_regs ms2) (Z_to_bv 5 1))). rewrite F1. exact Hra4. }
assert (HTR : In (call_trace0 (pc_free_ra0 (as_code B)) (ms_regs ms2) ch) (as_universe B)).
{ rewrite gx_trace0.
  replace (raZ (ms_regs ms2)) with (raZ regs); [exact Htrf|].
  change (bv_unsigned (YK11.getr regs (Z_to_bv 5 1)) = bv_unsigned (YK11.getr (ms_regs ms2) (Z_to_bv 5 1))).
  rewrite F1. reflexivity. }
assert (HCOV : In (a, n) (ablocks B ly S) -> forall i, 0 <= i < req_size n -> inFP FP (a + i))
  by exact (gx_start_fp segs B TG.G_HARNESS STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k a n HJ0 FRESH).
assert (HMOK : mo_ok MT S3 (mo_free MT)).
{ apply (mok_station MT Sc S3 T (mo_malloc MT n + 0) (mo_free MT) MTL Hmo MLE3 (mo_free_nonneg MT MTL)). lia. }
lazymatch goal with |- SRr ?sg ?Wx (mkCfg (@YK11.mkst _ ?rg _ ?mm ?rom) ?mdx) ?Q =>
  change (SRr sg Wx (mkCfg (@YK11.mkst fx rg (Z_to_bv 64 (transport_sigma TS___interceptor_trampoline_free)) mm rom)
    mdx) Q) end.
rewrite <- HFPC.
eapply SRr_mono.
{ exact (@gx_free_at fx rc tfib_sink_head segs B LAWS transport_segs_low MT (AFREE fx) TG.G_HARNESS W3 (ms_regs ms2)
    (ms_mem ms2) STK sp0 FP ly S W0 mem0 md0 own ly3 S3 _ (k + 1) a n (spZ regs - sp0) (YK11.getr regs (Z_to_bv 5 1)) ch
    HJ3 IN3 F10 ltac:(rewrite SPF; lia)
    ltac:(rewrite Zminus_mod, Hsp16, Hsp0a; reflexivity) ltac:(lia) ltac:(rewrite EAS; rewrite EST in Hwlo; lia)
    (eq_trans F3 Hgp) (eq_trans F4 Htp) F1 Hret ltac:(rewrite EEV in Hnev; lia) HCH HTR HCOV HMOK). }
intros W4 c4 _ (ly4 & S4 & regs4 & mem4 & md5 & -> & HJ5 & HP5 & HBL5 & HFR5 & HK5 & HML5).
(* the post: the free's return is receive's *)
replace (sp0 + (spZ regs - sp0)) with (spZ regs) in HK5 by lia.
pose proof (acall_kept_g_of segs B TG.G_HARNESS ly3 S3 W3 (ms_mem ms2) W4 mem4 _ _ _ HK5) as HK5g.
assert (KC4 : acall_kept_g segs B TG.G_HARNESS lyc Sc W memc W4 mem4 (spZ regs - RECV_STK) (spZ regs) (recv_wr bytes)).
{ apply (dk_kept_trans_nf_g segs B TG.G_HARNESS lyc Sc ly3 S3 W memc W3 (ms_mem ms2) W4 mem4 (spZ regs - RECV_STK)
    (spZ regs) (spZ regs - ASTACK) (spZ regs) (recv_wr bytes) (fun x => a <= x < a + req_size n)
    (fun x => a <= x < a + req_size n) HCE ltac:(lia) FA3 ltac:(intros f Hf; rewrite Hfr3, Hfr2; exact Hf)
    ltac:(intros bm Hb; exact (Permutation_in _ (Permutation_sym Hperm3) (BL2 bm Hb)))
    NFB NFF KC3 HK5g).
  - rewrite EAS, EST. lia.
  - lia.
  - intros x Hx. right. exact Hx. }
assert (PERM4 : Permutation (ablocks B ly4 S4) (ablocks B lyc Sc)).
{ destruct HBL5 as (l1 & l2 & Eb1 & Eb2). rewrite Eb2.
  assert (HPx : Permutation (l1 ++ (a, n) :: l2) ((a, n) :: ablocks B lyc Sc))
    by (rewrite <- Eb1; exact (Permutation_trans Hperm3 Hperm2)).
  exact (rs_perm_rm _ _ _ _ HPx). }
assert (HTW4 : tw_at TMAP_A (aview segs (w_H W4) mem4) B3).
{ apply (tw_kept_GA _ _ B3 HTWr).
  exact (gx_kept_rows segs TG.G_HARNESS W3 (ms_mem ms2) W4 mem4
    (gx_kept_of_acall_kept segs B TG.G_HARNESS ly3 S3 W3 (ms_mem ms2) W4 mem4 _ _ _ HGX HGNE HK5)). }
pose proof (mle_station MT Sc S3 S4 _ _ MTL MLE3 HML5) as MLE4.
unfold transport_recv_post, transport_cg_post.
exists ly4, S4, regs4, mem4, md5, 2.
split; [reflexivity|].
split; [unfold RECV_EV; lia|].
split; [replace (k + 2) with (k + 1 + 1) by lia; exact HJ5|].
split; [exact (aregs_preserved_trans _ _ _ HPT HP5)|].
split; [rewrite HFR5, Hfr3; exact Hfr2|].
split; [exact PERM4|].
split; [exact KC4|].
split.
{ apply (mle_weaken MT Sc S4 _ _ MTL MLE4).
  change (recv_cost MT (Z.of_nat (length bytes))) with (mo_malloc MT n + mo_free MT). lia. }
exists a, Bw'. split; [exact Haddr|]. split; [exact Hrm|].
rewrite HX3. split; [exact HTW4 | exact HGF3].
Qed.

End s.
