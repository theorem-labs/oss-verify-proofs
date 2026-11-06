(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: restates text of projects/cgif/cgif_file_fuzzer/proofs/lib/YCbq.v:528-543, 616-634;
   projects/cgif/cgif_rgb_fuzzer/proofs/lib/YC05.v:41-45, 208-214, 230-234, for libreac/fuzz_identity's asan-ubsan build
   (lib/B). The same text also appears in projects/cgif/cgif_file_fuzzer/proofs/lib/YCbo.v:420-423, 430-444, 447-448,
   453-455, 470-475, 477-486, 489-491, 502-505, 511-514, 1255-1258. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_identity/lib/B/Prog/reac_box_name_seg_rel.v, with its module paths, module names and numbers changed; 706 of its 765 lines of code are new or changed and 1865 lines of the source are left out. *)
(* on_announce_seg_tail: Theorem onann_piece_tail : forall fx rc B MT, @onann_tail_stmt fx rc B MT
   (lib/A/Prog/OnannCut.v), the release tail of the walk of on_announce, offsets +0x73c .. +0x814 of the listing
   lib/A/Prog/DgnTransportList.v (fuzz_transport.asan 0x881b0 .. 0x88288): the three release cuts onann_fnrel_at
   (+0x73c), onann_nrel_at (+0x764) and onann_arel_at (+0x78c).

   What the code does.
   fnrel, +0x73c .. +0x760: `li a0, -8` and 9 `sb a0, i(s3)`, i = 56 .. 64: fn's shadow bytes := 0xf8; the run stops at
     +0x764 and onann_nrel_at closes it.
   nrel, +0x764 .. +0x788: `li a0, -8` and 9 `sb a0, i(s3)`, i = 42 .. 50: n's shadow bytes := 0xf8; the run stops at
     +0x78c and onann_arel_at closes it.
   arel, +0x78c .. +0x814: `li a0, -8` and 5 `sb a0, i(s3)`, i = 32 .. 36: a's shadow bytes := 0xf8; +0x7a4 `lui` /
     `addiw` a0 = 0x45e0360e and +0x7ac `sd a0, 0(s2)`: the frame's first word (s2 = F); +0x7b0 `beqz s7`: s7 = F >= 4096,
     so the real-stack arm at +0x7cc is never entered (the engine decides the branch from the atom fact of s7);
     +0x7b4 `li a1, 128`, +0x7b8 `mv a0, s3`, +0x7bc the call of __asan_set_shadow_f5 (the frame's 128 shadow bytes
     := 0xf5), taken through TransportGCg.v aj_gx_entry_at with the statement's TransportRtCg.v aset_shadow_realizes
     (the written set Wr is the own frame's shadow, an awr_byte of the G journal by YCbq.v awr_byte's in_frames
     clause); +0x7c0 `ld a0, 1016(s7)`: the flag pointer FL from the frame's last word; +0x7c4 `sb zero, 0(a0)`: the
     flag byte, which releases the frame (TransportGFrame.v gx_flag_store_pi); +0x7c8 `j +0x7d8`; +0x7d8
     `addi sp, s0, -192`; the 13 reloads +0x7dc .. +0x80c of ra, s0, s1, s2 .. s11 from the words the prologue saved
     below the entry sp (OnannCut.v ONANN_SAVED); +0x810 `addi sp, sp, 192`; +0x814 `ret`.

   The runs. fnrel and nrel: one run each of the token engine over the G journal (TransportGRunA.v paj_run_to_x) from
   a state whose one region is the shadow range written; the cut's facts move to the run's memory (ot_kept_move: the
   run changed only own-frame shadow bytes, so the cut's acall_kept_g goes over it by TransportGFrame.v dk_kept_nf_gw,
   and the saved words, the frame's last word and the world relation are unchanged). arel: run 1 (paj_run_x) from
   +0x78c to the call (regions: a's shadow bytes and the frame's first word, both written); the call; run 3, the plain
   engine (PaSym.v sym_runN_pi) from +0x7c0 to the `ret`, which DgnTransportPaLib.v paj_ret_at takes (regions: the
   frame's last word, read: FL; the flag byte, written; the 13 saved words below s0 = the entry sp, read).

   The post (on_announce_cg.v transport_onann_post, TransportGCg.v transport_cg_post over G_HARNESS), as SlostRel.v
   proves session_lost's: the caller's G journal after the flag store, with own and the frame released
   (stack_free_state); the callee-saved registers are the 13 reloads, sp = s0 = the entry sp, gp and tp untouched; the
   frames the caller's (CanKit.v can_sf_frames); the state changed in st_fs only, so the meter bound is the cut's
   (mo_le_set_fs_r). What the call kept: the cut's acall_kept_g, carried over the three steps of arel by
   TransportGFrame.v dk_kept_nfz_gw: each byte they change is a byte of the own frame, of its shadow, its flag byte
   (TransportGCg.v dkg_nf) or a byte of the ESTACK scratch below sp of the set_shadow call, inside the call's window.
   The world relation at Bw': the cut's, kept since no byte of G is one of those bytes (TWorldA.v tw_kept_GA). *)
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s YK0o.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import YN3v YI04 YI00 YI08 YI09 YG0s.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq YG0p YC5d.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import YM05 YImgTop.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require YI16 YI5b YI5c.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import PaTable PaSym PaStep PaRun PaShadow PaJournal.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import
DgnTransportSyms DgnTransportList DgnTransportAddr DgnTransportPa DgnTransportImg DgnTransportPaLib YC4b YC1g YC1h.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A Require Import AB1v Img0.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A Require AE2k AsanCells TransportG.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A Require Import W_journalG.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import
DgnTransportCg TransportGCg TransportGRwA TransportGRunA CanKit TransportGFrame.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import TWorldG TWorldA TImgA.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import m_lost_cg check_state_data_cg notice_cg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import io_send_cg send_control_cg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import diginet_session_wake_cg maybe_online_cg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import session_lost_cg on_ack_cg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import diginet_personality_from_name_cg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import TransportRtCg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require diginet_announce_parse_cg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import on_announce_cg OnannCut.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel Require TWorld TCb TImg TNeed TSess0 TSess.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Spec Require DgnSpec DgnLib.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.
Module YK11 := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YK11.
Module TG := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.TransportG.
#[global] Remove Hints OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5b.src0_sink_head
  OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5c.src0_sink
  OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5c.src0_sink_laws : typeclass_instances.

(* ------------------------------------------------------------------ *)
(* 1. The symbolic states and the run of arel after the call            *)
(* ------------------------------------------------------------------ *)

(* +0x7c0, the return address of the call of __asan_set_shadow_f5, and the `ret`. *)
Definition ONANN_AR5 : Z := AF_on_announce + 0x7c0.
Definition ONANN_RET : Z := AF_on_announce + 0x814.

(* The empty shadow token of the runs that check no shadow byte. *)
Definition OT_Bx : sv := SLit 0.
Definition OT_B0 : Z * Z := (0, 0).

(* s3 (atom 19) holds the frame's first shadow byte SHADOW_OFF + F / 8, 8-aligned. *)
Definition ot_facts_sh : facts := mkFacts [(19%nat, mkAF (SHADOW_OFF + 512) (SHADOW_OFF + 2 ^ 44) 3)] [] [].

(* fnrel and nrel: the one region, shadow bytes lo .. hi - 1 of the frame (s3), written. *)
Definition ot_rg_sh (lo hi : Z) : YP09.region := YP09.mkRegion (Some 19%nat) lo hi lo hi [].
Definition ss_otfn : sstate := mkSS ONANN_FNREL sr_atoms [ot_rg_sh 56 65] None ot_facts_sh.
Definition ss_otn : sstate := mkSS ONANN_NREL sr_atoms [ot_rg_sh 42 51] None ot_facts_sh.

(* arel, run 1 (+0x78c .. the call at +0x7bc): a's shadow bytes 32 .. 36 (s3) and the frame's first word (s2, atom
   18), both written; s2 = s7 = F (atoms 18, 23) is at least 4096 (decides `beqz s7`) and 64-aligned. *)
Definition ot_rg_ash : YP09.region := YP09.mkRegion (Some 19%nat) 32 37 32 37 [].
Definition ot_rg_hd : YP09.region := YP09.mkRegion (Some 18%nat) 0 8 0 8 [].
Definition ot_facts1 : facts :=
  mkFacts [(18%nat, mkAF 4096 (2 ^ 47) 6); (19%nat, mkAF (SHADOW_OFF + 512) (SHADOW_OFF + 2 ^ 44) 3);
           (23%nat, mkAF 4096 (2 ^ 47) 6)] [] [].
Definition ss_ot1 : sstate := mkSS ONANN_AREL sr_atoms [ot_rg_ash; ot_rg_hd] None ot_facts1.

(* arel, run 3 (+0x7c0 .. the `ret`): the frame's last word (s7, offset 1016, read: atom 32 = FL), the flag byte (atom
   32, written), the 13 saved words below s0 = the entry sp (read: atoms 33 .. 45, ONANN_SAVED's order). *)
Definition ot_rg_fp : YP09.region :=
  YP09.mkRegion (Some 23%nat) 1016 1024 0 0 [YP09.mkChunk 1016 (CVal 8 (SOff 32 0))].
Definition ot_rg_fl : YP09.region := YP09.mkRegion (Some 32%nat) 0 1 0 1 [].
Definition ot_rg_sv : YP09.region :=
  YP09.mkRegion (Some 8%nat) (-104) 0 0 0
    [YP09.mkChunk (-8) (CVal 8 (SOff 33 0)); YP09.mkChunk (-16) (CVal 8 (SOff 34 0));
     YP09.mkChunk (-24) (CVal 8 (SOff 35 0)); YP09.mkChunk (-32) (CVal 8 (SOff 36 0));
     YP09.mkChunk (-40) (CVal 8 (SOff 37 0)); YP09.mkChunk (-48) (CVal 8 (SOff 38 0));
     YP09.mkChunk (-56) (CVal 8 (SOff 39 0)); YP09.mkChunk (-64) (CVal 8 (SOff 40 0));
     YP09.mkChunk (-72) (CVal 8 (SOff 41 0)); YP09.mkChunk (-80) (CVal 8 (SOff 42 0));
     YP09.mkChunk (-88) (CVal 8 (SOff 43 0)); YP09.mkChunk (-96) (CVal 8 (SOff 44 0));
     YP09.mkChunk (-104) (CVal 8 (SOff 45 0))].
Definition ot_facts3 : facts := mkFacts [(23%nat, mkAF 4096 (2 ^ 47) 6)] [] [].
Definition ss_ot3 : sstate := mkSS ONANN_AR5 sr_atoms [ot_rg_fp; ot_rg_fl; ot_rg_sv] None ot_facts3.
Definition OT_FUEL : N := 64.
Definition ot_ss_end : sstate := Eval vm_compute in fst (sym_runN_pi transport_tpi OT_FUEL ss_ot3).
Definition ot_st_end : prun_status tsym := Eval vm_compute in snd (sym_runN_pi transport_tpi OT_FUEL ss_ot3).
Lemma ot_run3 : sym_runN_pi transport_tpi OT_FUEL ss_ot3 = (ot_ss_end, ot_st_end).
Proof. vm_compute. reflexivity. Qed.
Lemma ot_stop3 : can_plain_stop ot_st_end.
Proof. exact I. Qed.
(* The run stops at the `ret` at +0x814. *)
Lemma ot_end_pc3 : ss_pc ot_ss_end = ONANN_RET.
Proof. reflexivity. Qed.

(* The environment of run 3: the registers at +0x7c0, then FL, then the entry values of the saved registers. *)
Definition ot_extra (regs : bvmap 5 word) (FL : Z) : list word :=
  w64 FL :: map (fun o : Z * Z => YK11.getr regs (Z_to_bv 5 (snd o))) ONANN_SAVED.

(* The value of register r in the machine state of HS: its symbolic value, computed. *)
Ltac ot_regv HS :=
  lazymatch type of HS with st_ok_pi ?sg ?vl ?Ex ?ssx (restrict ?Hh ?msx) =>
    rewrite (st_ok_pi_restrict_reg Hh Ex ssx msx _ HS);
    lazymatch goal with |- sv_denot _ ?e = _ => let e' := eval vm_compute in e in change e with e' end
  end.
(* The value of register r at the machine state of HS (a state of the token engine, or the concrete state a run that
   stopped at a call leaves), as the equation H : getr r = v, closed by tac. *)
Ltac ot_reg HS r v H tac :=
  lazymatch type of HS with
  | st_ok_pi ?segsx ?vl ?Ex ?ssx (restrict ?Hh ?msx) =>
      let e := eval vm_compute in (sr_get (ss_regs ssx) r) in
      assert (H : YK11.getr (ms_regs msx) r = v) by
        (refine (eq_trans (st_ok_pi_restrict_reg Hh Ex ssx msx r HS) _); change (sv_denot Ex e = v); tac)
  | OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YP0l.st_ok ?segsx ?Ex ?ssx (restrict ?Hh ?msx) =>
      let e := eval vm_compute in (sr_get (ss_regs ssx) r) in
      assert (H : YK11.getr (ms_regs msx) r = v) by
        (refine (eq_trans (st_ok_restrict_reg segsx Hh Ex ssx msx r HS) _); change (sv_denot Ex e = v); tac)
  end.
(* A register the run does not write, at the run's end, from the equation Q of its value at the run's start: the
   run's valuation agrees with the start valuation below atom 1024 (Elo), which reads the registers (EE). *)
Ltac ot_kreg HS Elo EE r n Q H :=
  lazymatch type of Q with _ = ?v =>
    ot_reg HS r v H
      ltac:(cbn [sv_denot]; rewrite (Elo n ltac:(lia)), (EE n r eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; exact Q) end.
(* The windows a run wrote, each inside the bytes X: the windows of the start state's regions, computed, each case
   closed by tac. *)
Ltac ot_win Hin Hx tac :=
  lazymatch type of Hin with In ?x ?l => let l' := eval vm_compute in l in change (In x l') in Hin end;
  cbn [In] in Hin;
  repeat (destruct Hin as [Hin | Hin]; [injection Hin as <- <- <-; cbn [base_val] in Hx; tac |]);
  destruct Hin.

Section tail. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Local Abbreviation tfib_sink_head := AE2k.tfib_sink_head.
Variable B : asyms.
Variable MT : ameter_ops.
Local Abbreviation segs := tfibsegs.
Local Abbreviation VAL := (@pa_val _ transport_listing PI_transport).
Local Abbreviation BASE := (@pa_val _ transport_listing PI_transport A_TEXT).

(* The cut points, the return address and the `ret` in the image's addresses. *)
Lemma ot_pcs : BASE + ONANN_FNREL = 0x881b0 /\ BASE + ONANN_NREL = 0x881d8 /\ BASE + ONANN_AREL = 0x88200 /\
  BASE + ONANN_AR5 = 0x88234 /\ BASE + ONANN_RET = 0x88288.
Proof. repeat split; reflexivity. Qed.

Definition ot_E3 (regs3 regs : bvmap 5 word) (FL : Z) : env :=
  Eimg (PI := PI_transport) (Ereg regs3 (ot_extra regs FL)).

Lemma ot_ew_reg : forall regs3 regs FL n (r : bv 5), Z.of_nat n = bv_unsigned r ->
  ew (ot_E3 regs3 regs FL) n = YK11.getr regs3 r.
Proof. intros regs3 regs FL n r Hn. unfold ot_E3. apply can_ew_Eimg_Ereg_nat. exact Hn. Qed.

Lemma ot_ew_x : forall regs3 regs FL j, (j < 14)%nat ->
  ew (ot_E3 regs3 regs FL) (32 + j) = nth j (ot_extra regs FL) (Z_to_bv 64 0).
Proof. intros regs3 regs FL j Hj. unfold ot_E3. rewrite Eimg_low by (unfold A_TEXT; lia). apply ew_Ereg_extra. Qed.

(* The bounds of a 64-aligned class-4 frame's first shadow byte. *)
Lemma ot_fsh : forall F, 4096 <= F -> F mod 64 = 0 -> F + 1024 <= 2 ^ 47 ->
  F / 8 = 8 * (F / 64) /\ F = 64 * (F / 64) /\ 512 <= F / 8 <= 2 ^ 44 /\ (SHADOW_OFF + F / 8) mod 8 = 0.
Proof.
intros F HF0 HF64 HFc.
pose proof (Z.div_mod F 64 ltac:(lia)) as DF. rewrite HF64, Z.add_0_r in DF.
assert (HF8 : F / 8 = 8 * (F / 64)) by (rewrite DF at 1; replace (64 * (F / 64)) with ((8 * (F / 64)) * 8) by ring; apply Z.div_mul; lia).
assert (HF8b : 512 <= F / 8 <= 2 ^ 44)
  by (split; [apply Z.div_le_lower_bound; lia | apply Z.div_le_upper_bound; lia]).
split; [exact HF8|]. split; [exact DF|]. split; [exact HF8b|].
rewrite HF8. unfold SHADOW_OFF. replace (2147450880 + 8 * (F / 64)) with ((268431360 + F / 64) * 8) by ring.
apply Z.mod_mul. lia.
Qed.

(* The symbolic state of fnrel / nrel holds of the machine state at its cut. *)
Lemma ot_entry_sh : forall (W : world segs) regs mem F pc lo hi,
  YK11.getr regs 19 = w64 (SHADOW_OFF + F / 8) -> 4096 <= F -> F mod 64 = 0 -> F + 1024 <= 2 ^ 47 ->
  0 <= lo -> lo <= hi -> hi <= 128 ->
  regions_wf [ot_rg_sh lo hi] = true ->
  (forall i, lo <= i < hi -> apresent (w_H W) mem (SHADOW_OFF + F / 8 + i)) ->
  st_ok_pi segs VAL (Eimg (PI := PI_transport) (Ereg regs [])) (mkSS pc sr_atoms [ot_rg_sh lo hi] None ot_facts_sh)
    (restrict (w_H W) (@YK11.mkst fx regs (Z_to_bv 64 (BASE + pc)) mem (YK11.seg_rom segs))).
Proof.
intros W regs mem F pc lo hi R19 HF0 HF64 HFc Hlo Hlh Hhi Hwf Hpsh.
destruct (ot_fsh F HF0 HF64 HFc) as (HF8 & DF & HF8b & M8).
set (E := Eimg (PI := PI_transport) (Ereg regs [])).
assert (U19 : bv_unsigned (ew E 19) = SHADOW_OFF + F / 8)
  by (unfold E; rewrite (can_ew_Eimg_Ereg_nat regs [] 19 19%bv eq_refl), R19; unfold w64; apply unsigned_lit_small;
      unfold SHADOW_OFF; lia).
rewrite restrict_mkst_fx.
apply (@pa_entry_st_ok_full fx rc transport_listing PI_transport).
- apply regs_ok_Eimg_Ereg.
- exact Hwf.
- apply Forall_cons; [|apply Forall_nil]. unfold region_ok, ot_rg_sh.
  cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val]. rewrite U19.
  split; [unfold SHADOW_OFF; lia|]. split; [unfold SHADOW_OFF; lia|]. split; [|constructor].
  intros o Ho. apply (apresent_writable segs). apply Hpsh. lia.
- apply pairwise_disjoint_of_extents. cbn [map zpairwise_disjoint zall_disjoint]. repeat split.
- unfold ot_facts_sh, facts_ok. cbn [f_atoms f_conds f_alias atoms_ok conds_ok alias_ok].
  unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite U19. change (2 ^ 3) with 8.
  unfold SHADOW_OFF in *. repeat match goal with |- _ /\ _ => split end; try exact I; lia.
Qed.

(* The symbolic state of arel's run 1 holds of the machine state at +0x78c. *)
Lemma ot_entry1 : forall (W : world segs) regs mem F,
  YK11.getr regs 18 = w64 F -> YK11.getr regs 19 = w64 (SHADOW_OFF + F / 8) -> YK11.getr regs 23 = w64 F ->
  4096 <= F -> F mod 64 = 0 -> F + 1024 <= 2 ^ 47 -> in_app F 1024 ->
  (forall a, F <= a < F + 8 -> apresent (w_H W) mem a) ->
  (forall i, 32 <= i < 37 -> apresent (w_H W) mem (SHADOW_OFF + F / 8 + i)) ->
  st_ok_pi segs VAL (Eimg (PI := PI_transport) (Ereg regs [])) ss_ot1
    (restrict (w_H W) (@YK11.mkst fx regs (Z_to_bv 64 (BASE + ONANN_AREL)) mem (YK11.seg_rom segs))).
Proof.
intros W regs mem F R18 R19 R23 HF0 HF64 HFc HFapp Hpf Hpsh.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
destruct (ot_fsh F HF0 HF64 HFc) as (HF8 & DF & HF8b & M8).
set (E := Eimg (PI := PI_transport) (Ereg regs [])).
assert (EE : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E n = YK11.getr regs r)
  by (intros n r Hn; unfold E; apply can_ew_Eimg_Ereg_nat; exact Hn).
assert (U18 : bv_unsigned (ew E 18) = F)
  by (rewrite (EE 18%nat 18%bv eq_refl), R18; unfold w64; apply unsigned_lit_small; lia).
assert (U19 : bv_unsigned (ew E 19) = SHADOW_OFF + F / 8)
  by (rewrite (EE 19%nat 19%bv eq_refl), R19; unfold w64; apply unsigned_lit_small; unfold SHADOW_OFF; lia).
assert (U23 : bv_unsigned (ew E 23) = F)
  by (rewrite (EE 23%nat 23%bv eq_refl), R23; unfold w64; apply unsigned_lit_small; lia).
rewrite restrict_mkst_fx. unfold ss_ot1.
apply (@pa_entry_st_ok_full fx rc transport_listing PI_transport).
- apply regs_ok_Eimg_Ereg.
- vm_compute. reflexivity.
- repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks ot_rg_ash ot_rg_hd base_val];
    rewrite ?U18, ?U19.
  + split; [unfold SHADOW_OFF; lia|]. split; [unfold SHADOW_OFF; lia|]. split; [|constructor].
    intros o Ho. apply (apresent_writable segs). apply Hpsh. lia.
  + split; [lia|]. split; [lia|]. split; [|constructor].
    intros o Ho. apply (apresent_writable segs). apply Hpf. lia.
- apply pairwise_disjoint_of_extents.
  unfold extent_of_region, ot_rg_ash, ot_rg_hd.
  cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite U18, U19.
  cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
  unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL, SHADOW_OFF in *.
  repeat split; first [exact I | lia].
- unfold ot_facts1, facts_ok. cbn [f_atoms f_conds f_alias atoms_ok conds_ok alias_ok].
  unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite U18, U19, U23.
  change (2 ^ 3) with 8. change (2 ^ 6) with 64.
  unfold SHADOW_OFF in *. repeat match goal with |- _ /\ _ => split end; try exact I; lia.
Qed.

(* The symbolic state of arel's run 3 holds of the machine state at +0x7c0. *)
Lemma ot_entry3 : forall (W : world segs) (regs3 regs : bvmap 5 word) mem (F FL SP : Z),
  YK11.getr regs3 8 = w64 SP -> YK11.getr regs3 23 = w64 F ->
  4096 <= F -> F mod 64 = 0 -> F + 1024 <= alloc_ceiling -> in_app F 1024 ->
  4096 <= FL < alloc_ceiling -> (FL < F + 1016 \/ F + 1024 <= FL) ->
  alloc_ceiling <= SP - 104 -> SP <= 2 ^ 47 ->
  apresent (w_H W) mem FL ->
  rdword (aview segs (w_H W) mem) (F + 1016) = Some FL ->
  Forall (fun o : Z * Z => rdword (aview segs (w_H W) mem) (SP - fst o) =
      Some (bv_unsigned (YK11.getr regs (Z_to_bv 5 (snd o))))) ONANN_SAVED ->
  st_ok_pi segs VAL (ot_E3 regs3 regs FL) ss_ot3
    (restrict (w_H W) (@YK11.mkst fx regs3 (Z_to_bv 64 (BASE + ONANN_AR5)) mem (YK11.seg_rom segs))).
Proof.
intros W regs3 regs mem F FL SP R8 R23 HF0 HF64 HFc HFapp HFL HFLF HSP HSP47 HpFL HFLw Hsaved.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
set (E := ot_E3 regs3 regs FL).
assert (U8 : bv_unsigned (ew E 8) = SP)
  by (unfold E; rewrite (ot_ew_reg regs3 regs FL 8 8%bv eq_refl), R8; unfold w64; apply unsigned_lit_small; lia).
assert (U23 : bv_unsigned (ew E 23) = F)
  by (unfold E; rewrite (ot_ew_reg regs3 regs FL 23 23%bv eq_refl), R23; unfold w64; apply unsigned_lit_small; lia).
assert (E32 : ew E 32 = w64 FL) by exact (ot_ew_x regs3 regs FL 0 ltac:(lia)).
assert (U32 : bv_unsigned (ew E 32) = FL) by (rewrite E32; unfold w64; apply unsigned_lit_small; lia).
unfold ONANN_SAVED in Hsaved.
repeat match goal with H : Forall _ (_ :: _) |- _ => apply Forall_cons_iff in H; destruct H as [?Sv H] end.
cbn [fst snd] in *.
rewrite restrict_mkst_fx. unfold ss_ot3.
apply (@pa_entry_st_ok_full fx rc transport_listing PI_transport).
- apply regs_ok_Eimg_Ereg.
- vm_compute. reflexivity.
- repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks ot_rg_fp ot_rg_fl ot_rg_sv base_val];
    rewrite ?U8, ?U23, ?U32.
  + split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
    constructor; [|constructor].
    apply (chunk_ok_val segs E _ F 1016 8 (SOff 32 0) FL);
      [cbn [sv_denot]; rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside |].
    exact (val_mem_of_rdword segs _ _ _ _ HFLw).
  + split; [lia|]. split; [lia|]. split; [|constructor].
    intros o Ho. apply (apresent_writable segs). replace (FL + o) with FL by lia. exact HpFL.
  + split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
    repeat apply Forall_cons; try apply Forall_nil.
    all: lazymatch goal with |- YP09.chunk_ok _ _ _ ?b (YP09.mkChunk ?off (CVal 8 (SOff ?n 0))) =>
      match goal with Sv : rdword _ (?b0 - ?o) = Some (bv_unsigned ?x) |- _ =>
        apply (chunk_ok_val segs E _ b off 8 (SOff n 0) (bv_unsigned x));
        [ cbn [sv_denot]; rewrite Z.add_0_r; reflexivity
        | let Hrr := fresh "Hrr" in pose proof (bv_unsigned_in_range 64 x) as Hrr;
          change (bv_modulus 64) with (2 ^ 64) in Hrr; exact Hrr
        | zside
        | replace (b + off) with (b0 - o) by lia; exact (val_mem_of_rdword segs _ _ _ _ Sv) ]
      end end.
- apply pairwise_disjoint_of_extents.
  unfold extent_of_region, ot_rg_fp, ot_rg_fl, ot_rg_sv.
  cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val].
  rewrite U8, U23, U32.
  cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
  unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL, SHADOW_OFF in *.
  repeat split; first [exact I | lia].
- unfold ot_facts3, facts_ok. cbn [f_atoms f_conds f_alias atoms_ok conds_ok alias_ok].
  unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite U23.
  change (2 ^ 6) with 64.
  repeat match goal with |- _ /\ _ => split end; try exact I; lia.
Qed.

(* The facts the release cuts carry move to a later memory that differs from the cut's only in some of the own frame's
   shadow bytes (fnrel, nrel): what the call kept (TransportGFrame.v dk_kept_nf_gw), the 13 saved words (in the stack,
   above alloc_ceiling), the frame's last word (in the frame) and the world relation (no byte of G is a shadow byte). *)
Lemma ot_kept_move : forall lyc Sc (W : world segs) memc mdc ly2 S2 (W2 : world segs) mem2 md2 mem3 slo shi pos F
    (Eo Zs : Z -> Prop) (regs : bvmap 5 word) (Bw' : list byte),
  AR_laws segs B -> frame_flag_lawP segs B -> gx_ok segs B TG.G_HARNESS ->
  @AR rc segs B lyc Sc W memc mdc -> @AR rc segs B ly2 S2 W2 mem2 md2 ->
  frames S2 = (ONANN_CID, pos) :: frames Sc -> Permutation (ablocks B ly2 S2) (ablocks B lyc Sc) ->
  ly_F ly2 = ly_F lyc -> F = frame_addr lyc ONANN_CID pos ->
  4096 <= F -> F mod 64 = 0 -> F + 1024 <= alloc_ceiling -> in_app F 1024 ->
  alloc_ceiling <= spZ regs - 104 -> spZ regs <= 2 ^ 47 ->
  (forall a, Zs a -> SHADOW_OFF + F / 8 <= a < SHADOW_OFF + F / 8 + 128) ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ Zs a -> aview segs (w_H W2) mem3 a = aview segs (w_H W2) mem2 a) ->
  (forall a, apresent (w_H W2) mem2 a -> apresent (w_H W2) mem3 a) ->
  acall_kept_g segs B TG.G_HARNESS lyc Sc W memc W2 mem2 slo shi Eo ->
  Forall (fun o : Z * Z => rdword (aview segs (w_H W2) mem2) (spZ regs - fst o) =
      Some (bv_unsigned (YK11.getr regs (Z_to_bv 5 (snd o))))) ONANN_SAVED ->
  rdword (aview segs (w_H W2) mem2) (F + ONANN_FBYTES - 8) = Some (flag_addr lyc ONANN_CID pos) ->
  tw_at TMAP_A (aview segs (w_H W2) mem2) Bw' ->
  acall_kept_g segs B TG.G_HARNESS lyc Sc W memc W2 mem3 slo shi Eo /\
  Forall (fun o : Z * Z => rdword (aview segs (w_H W2) mem3) (spZ regs - fst o) =
      Some (bv_unsigned (YK11.getr regs (Z_to_bv 5 (snd o))))) ONANN_SAVED /\
  rdword (aview segs (w_H W2) mem3) (F + ONANN_FBYTES - 8) = Some (flag_addr lyc ONANN_CID pos) /\
  tw_at TMAP_A (aview segs (w_H W2) mem3) Bw'.
Proof.
intros lyc Sc W memc mdc ly2 S2 W2 mem2 md2 mem3 slo shi pos F Eo Zs regs Bw' LAWS FFL HGX HARc HAR2 Hfrs Hperm ELF EF
  HF0 HF64 HFc HFapp HSP HSP47 HZs KP GR HK Hsaved HFLw Htw.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (HFc47 : F + 1024 <= 2 ^ 47) by lia.
destruct (ot_fsh F HF0 HF64 HFc47) as (HF8 & DF & HF8b & M8).
assert (HSHF : SHADOW_OFF + F / 8 + 128 <= F \/ F + 1024 <= SHADOW_OFF + F / 8).
{ unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in HFapp. destruct HFapp as (_ & [HL | (HH1 & HH2)]);
  [right | left]; unfold SHADOW_OFF; lia. }
assert (Hbl : forall bm, In bm (ablocks B lyc Sc) -> In bm (ablocks B ly2 S2))
  by (intros bm Hb; eapply Permutation_in; [apply Permutation_sym; exact Hperm | exact Hb]).
split; [|split; [|split]].
- apply (dk_kept_nf_gw segs B LAWS transport_segs_low TG.G_HARNESS lyc Sc W memc mdc ly2 S2 W2 mem2 md2 mem3 slo shi
    ONANN_CID pos F (flag_addr lyc ONANN_CID pos) Eo HARc HAR2 Hfrs Hbl ELF EF eq_refl FFL HK); [|exact GR].
  intros a Ha Hn. apply KP; [exact Ha|]. intros Hz. apply Hn. unfold dkg_nf. right; left.
  change (fs_frame_bytes ONANN_CID / 8) with 128. exact (HZs a Hz).
- apply Forall_forall. intros o Hin. cbv beta.
  pose proof (proj1 (Forall_forall _ _) Hsaved o Hin) as Hv. cbv beta in Hv.
  assert (Ho : 8 <= fst o <= 104).
  { unfold ONANN_SAVED in Hin. cbn [In] in Hin.
    repeat (destruct Hin as [Hin | Hin]; [subst o; cbn [fst]; lia |]). destruct Hin. }
  rewrite <- Hv. apply YCbq.rdword_ext. intros i Hi. apply KP; [lia|]. intros Hz. pose proof (HZs _ Hz).
  unfold SHADOW_OFF in *. lia.
- unfold ONANN_FBYTES in *. rewrite <- HFLw. apply YCbq.rdword_ext. intros i Hi. apply KP; [lia|].
  intros Hz. pose proof (HZs _ Hz). unfold SHADOW_OFF in *. lia.
- apply (tw_kept_GA (aview segs (w_H W2) mem2)); [exact Htw|].
  intros b n i Hbn Hi.
  assert (HG : inG TG.G_HARNESS (b + i))
    by (unfold inG; apply Exists_exists; exists (b, n); split; [exact Hbn | unfold in_zr; cbn [fst snd]; lia]).
  pose proof (inG_low segs B transport_segs_low TG.G_HARNESS (b + i) HGX HG) as Hl. unfold kLowMemEnd in Hl.
  apply KP; [lia|]. intros Hz. pose proof (HZs _ Hz). unfold SHADOW_OFF in *. lia.
Qed.

(* ------------------------------------------------------------------ *)
(* 2. arel, +0x78c .. +0x814                                           *)
(* ------------------------------------------------------------------ *)

(* The bytes run 1 writes: a's shadow bytes 32 .. 36 and the frame's first word. *)
Definition ot_Z1 (F x : Z) : Prop :=
  (SHADOW_OFF + F / 8 + 32 <= x < SHADOW_OFF + F / 8 + 37) \/ (F <= x < F + 8).

Lemma ot_arel : @onann_arel_at fx rc B MT.
Proof.
unfold onann_arel_at.
intros LAWS0 CALLEES STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs fp buf now b fj TF Bw Bw' pos sp1 F
  ly2 S2 W2 mem2 md2 e regs2 HFIX HCUR HREGS.
pose proof LAWS0 as (_ & _ & _ & _ & _ & _ & _ & LAWS & MTL & MTF & _ & ASF & FFL & HGX & _).
pose proof CALLEES as (_ & _ & _ & _ & _ & _ & _ & _ & HSF5).
pose proof HFIX as (HJ0 & Hret & _ & Hgp & Htp & _ & _ & _ & Hsp16 & Hlo & Hhi & _ & _ & _ & _ & _ & _ & _ & _ & _ &
  _ & _ & _ & _ & Esp1 & EF & HF0 & HF64 & HFc & HFapp).
pose proof HCUR as ((HJ1 & He & Hfrs & Hperm & ELF & Hmo & HK & Hsaved & HFLw) & HTW2 & Hgf2).
pose proof HREGS as ((R2 & R3 & R4 & R8 & R9 & R18 & R19) & R23).
unfold ONANN_FBYTES in HFc, HFapp, HFLw.
replace (F + 1024 - 8) with (F + 1016) in HFLw by lia.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (HFc47 : F + 1024 <= 2 ^ 47) by lia.
destruct (ot_fsh F HF0 HF64 HFc47) as (HF8 & DF & HF8b & MS8).
(* the call's window lies above alloc_ceiling, below 2 ^ 47 *)
pose proof HJ0 as (_ & _ & (memS & HJi & _) & _). rewrite !Z.add_0_r in HJi.
pose proof HJi as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hstk & _).
pose proof Hstk as (Hsp0a & Hstk0 & Hceil & Hslo & Hshi & H47 & _).
clear HJi memS.
assert (EST : ESTACK = 4096) by reflexivity.
assert (HBS : 208 + ESTACK <= ONANN_STK).
{ unfold ONANN_STK, ONANN_FRAME, ONANN_ALIGN.
  lazymatch goal with |- _ <= _ + _ + Z.max ?a ?b =>
    pose proof (Z.le_max_l a b) as Hm0; assert (Ha : a = 4096) by reflexivity end.
  lia. }
assert (Hsp1 : spZ regs - 208 <= sp1 <= spZ regs - 192 /\ sp1 mod 32 = 0).
{ rewrite Esp1. unfold ONANN_FRAME.
  pose proof (Z.div_mod (spZ regs - 192) 32 ltac:(lia)) as D.
  pose proof (Z.mod_pos_bound (spZ regs - 192) 32 ltac:(lia)) as M.
  pose proof (Z.div_mod (spZ regs) 16 ltac:(lia)) as D16. rewrite Hsp16, Z.add_0_r in D16.
  set (q := (spZ regs - 192) / 32) in *. set (r := (spZ regs - 192) mod 32) in *. set (t := spZ regs / 16) in *.
  split; [lia|]. rewrite Z.mul_comm, Z.mod_mul by lia. reflexivity. }
pose proof (ajournal_gx_AR segs B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ0) as HARc.
pose proof (ajournal_gx_AR segs B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ1) as HAR2.
(* the frame, its shadow bytes and its flag byte at the cut *)
assert (Hin : In (ONANN_CID, pos) (frames S2)) by (rewrite Hfrs; left; reflexivity).
assert (EFA : frame_addr ly2 ONANN_CID pos = F) by (rewrite EF; unfold frame_addr; rewrite ELF; reflexivity).
assert (EFL : flag_addr ly2 ONANN_CID pos = flag_addr lyc ONANN_CID pos)
  by (unfold flag_addr; rewrite ELF; reflexivity).
rewrite <- EFL in HFLw.
destruct (al_frames _ _ LAWS _ _ _ _ _ ONANN_CID pos HAR2 Hin) as (_ & _ & HFb & HFsh).
destruct (FFL ly2 S2 W2 mem2 md2 ONANN_CID pos HAR2 Hin) as (HFLp & HFLo & _ & (HFL4096 & _ & HFLc)).
set (FL := flag_addr ly2 ONANN_CID pos) in *.
change (fs_frame_bytes ONANN_CID / 8) with 128 in HFsh.
change (fs_frame_bytes ONANN_CID) with 1024 in HFb.
rewrite EFA in HFb, HFsh.
assert (ESH : shadow_addr F = SHADOW_OFF + F / 8) by reflexivity.
rewrite ESH in HFsh.
assert (HFLF : FL < F \/ F + 1024 <= FL).
{ destruct (Z_lt_le_dec FL F) as [h|h]; [left; exact h|].
  destruct (Z_lt_le_dec FL (F + 1024)) as [h2|h2]; [|right; exact h2].
  exfalso. exact (proj2 (HFb _ (conj h h2)) HFLo). }
assert (HSHF : SHADOW_OFF + F / 8 + 128 <= F \/ F + 1024 <= SHADOW_OFF + F / 8).
{ unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in HFapp. destruct HFapp as (_ & [HL | (HH1 & HH2)]);
  [right | left]; unfold SHADOW_OFF; lia. }
(* the own frame, its shadow bytes and its flag byte are apart from the call's blocks, the image and the call's frames *)
assert (Hbl : forall bm, In bm (ablocks B lyc Sc) -> In bm (ablocks B ly2 S2))
  by (intros bm Hb; eapply Permutation_in; [apply Permutation_sym; exact Hperm | exact Hb]).
destruct (dkg_nf_sep_gw segs B LAWS transport_segs_low lyc Sc ly2 S2 W2 mem2 md2 ONANN_CID pos F FL HAR2 Hfrs Hbl
  ELF EF EFL FFL) as (N1 & N2 & N3 & N4).
assert (USP : spZ regs2 = sp1) by (unfold spZ; rewrite R2; unfold w64; apply unsigned_lit_small; lia).
(* run 1, +0x78c .. +0x7bc: a's shadow bytes 32 .. 36 := 0xf8, the header word, `beqz s7` not taken, a1 = 128,
   a0 = s3, `jal __asan_set_shadow_f5` *)
pose proof (ot_entry1 W2 regs2 mem2 F R18 R19 R23 HF0 HF64 HFc47 HFapp
  ltac:(intros a Ha; exact (proj1 (HFb a ltac:(lia))))
  ltac:(intros i Hi; exact (proj1 (HFsh i ltac:(lia))))) as HS.
set (E0 := Eimg (PI := PI_transport) (Ereg regs2 [])) in HS.
assert (HEI : img_env VAL A_LIM E0) by (unfold E0; apply Eimg_env).
assert (EE : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E0 n = YK11.getr regs2 r)
  by (intros n r Hn; unfold E0; apply can_ew_Eimg_Ereg_nat; exact Hn).
assert (U18 : bv_unsigned (ew E0 18) = F)
  by (rewrite (EE 18%nat 18%bv eq_refl), R18; unfold w64; apply unsigned_lit_small; lia).
assert (U19 : bv_unsigned (ew E0 19) = SHADOW_OFF + F / 8)
  by (rewrite (EE 19%nat 19%bv eq_refl), R19; unfold w64; apply unsigned_lit_small; unfold SHADOW_OFF; lia).
assert (SHOK : sh_ok segs OT_Bx (@nil shent) E0 (mrestrict (w_H W2) mem2)) by constructor.
pose proof (@paj_run_x fx rc tfib_sink_head transport_listing PL_transport PI_transport B LAWS TG.G_HARNESS HGX 0 [])
  as RUN.
paj_run_tok RUN HS HJ1 SHOK OT_B0.
{ lazymatch goal with |- awr_ok_x ?Ex ?rs ?Gx ?XO ?OUT ?stk ?sp0q ?fp ?b0 ?bc ?lyq ?ownq =>
    let rs' := eval vm_compute in rs in change (awr_ok_x Ex rs' Gx XO OUT stk sp0q fp b0 bc lyq ownq) end.
  eapply awr_ok_x_cons_own with (cid := ONANN_CID); [left; reflexivity | |].
  { intros a Ha. cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha. rewrite U19 in Ha.
    right. unfold in_zr. cbn [fst snd]. rewrite EFA, ESH. change (fs_frame_bytes ONANN_CID / 8) with 128. lia. }
  eapply awr_ok_x_cons_own with (cid := ONANN_CID); [left; reflexivity | |].
  { intros a Ha. cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha. rewrite U18 in Ha.
    left. unfold in_zr. cbn [fst snd]. rewrite EFA. change (fs_frame_bytes ONANN_CID) with 1024. lia. }
  apply awr_ok_x_nil. }
set (md1 := with_vm_backing (m_vm_lazy md2) mat md2) in *. clearbody md1. clear mat.
assert (KR1 : forall a, 0 <= a < 2 ^ 64 -> ~ ot_Z1 F a ->
  aview segs (w_H W2) (ms_mem ms) a = aview segs (w_H W2) mem2 a).
{ intros a Ha Hn. apply (kept_of_frame _ _ _ _ _ (ot_Z1 F) HFr); [| exact Ha | exact Hn].
  intros b0 wlo whi x Hiw Hx. cbv beta.
  ot_win Hiw Hx ltac:(rewrite ?U18, ?U19 in Hx; unfold ot_Z1; first [left; lia | right; lia]). }
assert (GA1 : forall a, apresent (w_H W2) mem2 a -> apresent (w_H W2) (ms_mem ms) a)
  by (intros a Ha; exact (apresent_grows _ _ _ a HG Ha)).
clear HF HFr HG.
lazymatch type of HS with
| st_ok_pi _ _ ?EF _ (restrict _ ?mf) => set (E1 := EF) in HS; rename mf into msC
| OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YP0l.st_ok _ ?EF _ (restrict _ ?mf) =>
    set (E1 := EF) in HS; rename mf into msC
end.
assert (E1lo : forall n, (n < 1024)%nat -> ew E1 n = ew E0 n)
  by (intros n Hn; unfold E1; rewrite ?ew_ewset_other by lia; reflexivity).
assert (HEI1 : img_env VAL A_LIM E1) by (unfold E1; first [exact HEI | assumption]).
pmkst HS.
ot_reg HS (Z_to_bv 5 10) (w64 (SHADOW_OFF + F / 8)) Q10
  ltac:(cbn [sv_denot]; rewrite (E1lo 19%nat ltac:(lia)), (EE 19%nat (Z_to_bv 5 19) eq_refl), Z.add_0_r,
    Z_to_bv_bv_unsigned; exact R19).
ot_reg HS (Z_to_bv 5 11) (Z_to_bv 64 128) Q11 ltac:(reflexivity).
ot_reg HS (1%bv : bv 5) (Z_to_bv 64 (BASE + ONANN_AR5)) Q1 ltac:(apply codeptr_val; exact HEI1).
ot_kreg HS E1lo EE (Z_to_bv 5 2) 2%nat R2 Q2. ot_kreg HS E1lo EE (Z_to_bv 5 3) 3%nat R3 Q3.
ot_kreg HS E1lo EE (Z_to_bv 5 4) 4%nat R4 Q4. ot_kreg HS E1lo EE (Z_to_bv 5 8) 8%nat R8 Q8.
ot_kreg HS E1lo EE (Z_to_bv 5 23) 23%nat R23 Q23.
assert (QSP : spZ (ms_regs msC) = sp1)
  by (change (bv_unsigned (YK11.getr (ms_regs msC) (Z_to_bv 5 2)) = sp1); rewrite Q2; unfold w64;
      apply unsigned_lit_small; lia).
(* +0x7bc: __asan_set_shadow_f5 (shadow_addr F, 128), through the G journal's runtime-entry lift *)
lazymatch goal with |- SRr ?sg ?Wx (mkCfg (@YK11.mkst _ ?rg _ ?mm ?rom) ?mdx) ?Q =>
  change (SRr sg Wx (mkCfg (@YK11.mkst fx rg (Z_to_bv 64 (transport_sigma TS___asan_set_shadow_f5)) mm rom) mdx) Q) end.
eapply SRr_bind.
{ apply (@aj_gx_entry_at fx rc tfib_sink_head segs B LAWS transport_segs_low TG.G_HARNESS 0 [] ESTACK
    (transport_sigma TS___asan_set_shadow_f5)
    (fun a => SHADOW_OFF + F / 8 <= a < SHADOW_OFF + F / 8 + 128)
    (fun (regs' : bvmap 5 word) (mem' : word -> option byte) =>
       forall i, 0 <= i < 128 -> aview segs (w_H W2) mem' (SHADOW_OFF + F / 8 + i) = Some 0xf5)
    W2 (ms_regs msC) (ms_mem msC) STK sp0 FP ly S W0 mem0 md0 ((ONANN_CID, pos) :: own) ly2 S2 md1 (k + e)
    (sp1 - sp0) (Z_to_bv 64 (BASE + ONANN_AR5)) HGX eq_refl HJ1).
  - rewrite QSP. lia.
  - pose proof (Z.div_mod sp1 32 ltac:(lia)) as D1. pose proof (Z.div_mod sp0 16 ltac:(lia)) as D2.
    destruct Hsp1 as (_ & M1). rewrite M1, Z.add_0_r in D1. rewrite Hsp0a, Z.add_0_r in D2.
    rewrite D1, D2. replace (32 * (sp1 / 32) - 16 * (sp0 / 16)) with ((2 * (sp1 / 32) - sp0 / 16) * 16) by ring.
    apply Z.mod_mul. lia.
  - lia.
  - apply Z.le_refl.
  - lia.
  - exact (eq_trans Q3 Hgp).
  - exact (eq_trans Q4 Htp).
  - exact Q1.
  - apply (ret_ok_codeptr_v (PI := PI_transport)); [change ONANN_AR5 with 28624; lia | reflexivity].
  - exact G_HARNESS_rw.
  - intros a Ha HnG. split; [|lia].
    unfold awr_byte. right; right; right. unfold in_frames. exists ONANN_CID, pos. split; [left; reflexivity|].
    right. unfold in_zr. cbn [fst snd]. rewrite EFA, ESH. change (fs_frame_bytes ONANN_CID / 8) with 128. lia.
  - intros HPRE _. eapply SRr_mono.
    { exact (HSF5 fx ly2 S2 W2 (ms_regs msC) (ms_mem msC) md1 ONANN_CID pos (SHADOW_OFF + F / 8) 128 HPRE Hin Q10 Q11
        ltac:(lia) ltac:(rewrite EFA, ESH; lia)
        ltac:(rewrite EFA, ESH; change (fs_frame_bytes ONANN_CID / 8) with 128; lia)). }
    cbv beta. intros W' c' _ (-> & regs' & mem' & md' & -> & HAR' & HP' & Hsm & Hv & Hk & _ & Hgr).
    hnf. split; [reflexivity|]. exists regs', mem', md'.
    split; [reflexivity|]. split; [exact HAR'|]. split; [exact HP'|]. split; [exact Hsm|].
    split; [exact Hv|]. split; [intros a Ha HnW _; exact (Hk a Ha HnW) | exact Hgr]. }
cbv beta. intros W3 c3 _ (-> & regsM & memM & mdM & -> & HJ2 & HPM & HPr & HfrM & HgrM).
(* what the call left: the view outside a's shadow, the header word, the frame's shadow and the scratch below sp1 *)
assert (KM : forall a, 0 <= a < 2 ^ 64 -> ~ ot_Z1 F a -> ~ (SHADOW_OFF + F / 8 <= a < SHADOW_OFF + F / 8 + 128) ->
  ~ (sp1 - ESTACK <= a < sp1) -> aview segs (w_H W2) memM a = aview segs (w_H W2) mem2 a).
{ intros a Ha H1 H2 H3. rewrite (HfrM a Ha H2 ltac:(intros Hx; apply H3; lia)). exact (KR1 a Ha H1). }
assert (GM : forall a, apresent (w_H W2) mem2 a -> apresent (w_H W2) memM a)
  by (intros a Ha; exact (HgrM a (GA1 a Ha))).
assert (M8 : YK11.getr regsM 8 = w64 (spZ regs)) by exact (eq_trans (HPM 8 ltac:(hnf; lia)) Q8).
assert (M23 : YK11.getr regsM 23 = w64 F) by exact (eq_trans (HPM 23 ltac:(hnf; lia)) Q23).
assert (M3 : YK11.getr regsM 3 = YK11.getr regs 3) by exact (eq_trans (HPM 3 ltac:(hnf; lia)) Q3).
assert (M4 : YK11.getr regsM 4 = YK11.getr regs 4) by exact (eq_trans (HPM 4 ltac:(hnf; lia)) Q4).
assert (HFLwM : rdword (aview segs (w_H W2) memM) (F + 1016) = Some FL).
{ rewrite <- HFLw. apply YCbq.rdword_ext. intros i Hi. apply KM; [lia | unfold ot_Z1 | | ];
  unfold SHADOW_OFF in *; lia. }
assert (HsavedM : Forall (fun o : Z * Z => rdword (aview segs (w_H W2) memM) (spZ regs - fst o) =
    Some (bv_unsigned (YK11.getr regs (Z_to_bv 5 (snd o))))) ONANN_SAVED).
{ apply Forall_forall. intros o Hino. cbv beta.
  pose proof (proj1 (Forall_forall _ _) Hsaved o Hino) as Hv. cbv beta in Hv.
  assert (Ho : 8 <= fst o <= 104).
  { unfold ONANN_SAVED in Hino. cbn [In] in Hino.
    repeat (destruct Hino as [Hino | Hino]; [subst o; cbn [fst]; lia |]). destruct Hino. }
  rewrite <- Hv. apply YCbq.rdword_ext. intros i Hi. apply KM; [lia | unfold ot_Z1 | | ];
  unfold SHADOW_OFF in *; lia. }
(* run 3, +0x7c0 .. +0x814: the flag store at +0x7c4 releases the frame; the epilogue and the `ret` *)
pose proof (ot_entry3 W2 regsM regs memM F FL (spZ regs) M8 M23 HF0 HF64 HFc HFapp ltac:(lia)
  ltac:(destruct HFLF as [h|h]; [left | right]; lia) ltac:(lia) ltac:(lia) (GM FL HFLp) HFLwM HsavedM) as HS3.
set (E3 := ot_E3 regsM regs FL) in HS3.
assert (HEI3 : img_env VAL A_LIM E3) by (unfold E3, ot_E3; apply Eimg_env).
assert (U23c : bv_unsigned (ew E3 23) = F)
  by (unfold E3; rewrite (ot_ew_reg regsM regs _ 23 23%bv eq_refl), M23; unfold w64; apply unsigned_lit_small; lia).
assert (E32 : ew E3 32 = w64 FL) by exact (ot_ew_x regsM regs _ 0 ltac:(lia)).
assert (U32 : bv_unsigned (ew E3 32) = FL) by (rewrite E32; unfold w64; apply unsigned_lit_small; lia).
refine (gx_flag_store_pi (SK := tfib_sink_head) B LAWS ASF FFL TG.G_HARNESS W2 OT_FUEL E3 ss_ot3 ot_ss_end
  ot_st_end (@YK11.mkst fx regsM (Z_to_bv 64 (BASE + ONANN_AR5)) memM (YK11.seg_rom segs))
  STK sp0 FP ly S W0 mem0 md0 own ly2 S2 mdM (k + e) ONANN_CID pos _ HEI3 HS3 ot_run3 ot_stop3 HJ2 _ _ _ _).
- unfold ONANN_CID. lia.
- (* run 3 writes the flag byte only *)
  intros a (rg & Hinr & Ha). unfold ss_ot3 in Hinr. cbn [ss_mem In] in Hinr.
  destruct Hinr as [<- | [<- | [<- | []]]];
    cbn [base_val YP09.r_base YP09.r_wlo YP09.r_whi ot_rg_fp ot_rg_fl ot_rg_sv] in Ha;
    rewrite ?U23c, ?U32 in Ha.
  + lia.
  + right. change (flag_addr ly2 ONANN_CID pos) with FL. lia.
  + lia.
- (* the flag byte is 0 after the run *)
  intros msr HSr.
  lazymatch goal with |- _ = Some _ =>
    let rr := eval vm_compute in (nth_error (ss_mem ot_ss_end) 1) in
    lazymatch rr with Some ?r1 =>
      pose proof (can_region_nth (segs := segs) _ _ msr 1 r1 HSr eq_refl) as HR1 end end.
  pose proof (can_field_of_region (segs := segs) E3 (ms_mem msr) 32 FL _ 0 1 0 1 0 1%N
    (SLit 0) 0 HR1 U32 ltac:(cbn [In]; auto) eq_refl ltac:(cbn; lia) ltac:(cbn; lia)) as V.
  specialize (V 0%nat ltac:(cbn; lia)).
  lazymatch type of V with _ = Some (Z_to_bv 8 ?x) => replace x with 0 in V by (vm_compute; reflexivity) end.
  replace (FL + 0 + Z.of_nat 0) with FL in V by lia.
  exact V.
- (* the return *)
  intros ms2 mat2 HS2 HJ3 _ HF2 HG2.
  set (md3 := with_vm_backing (m_vm_lazy mdM) mat2 mdM) in *. clearbody md3.
  (* what run 3 kept: every byte but the flag byte; presence grows *)
  assert (KP3 : forall a, 0 <= a < 2 ^ 64 -> a <> FL ->
    aview segs (w_H W2) (ms_mem ms2) a = aview segs (w_H W2) memM a).
  { intros a Ha Hn.
    apply (kept_of_frame (segs := segs) E3 (ss_mem ss_ot3) (w_H W2) memM (ms_mem ms2) (fun x => x = FL) HF2);
      [| exact Ha | exact Hn].
    intros b0 wlo whi x Hw Hx. unfold ss_ot3, windows in Hw.
    cbn [ss_mem map In YP09.r_base YP09.r_wlo YP09.r_whi ot_rg_fp ot_rg_fl ot_rg_sv] in Hw.
    destruct Hw as [Hw | [Hw | [Hw | []]]]; injection Hw as <- <- <-;
      cbn [base_val] in Hx; rewrite ?U23c, ?U32 in Hx; cbv beta; lia. }
  (* what arel changed: the own frame's bytes, its shadow, its flag byte, the scratch below sp1 *)
  assert (KALL : forall a, 0 <= a < 2 ^ 64 -> ~ (dkg_nf ONANN_CID F FL a \/ (sp1 - ESTACK <= a < sp1)) ->
    aview segs (w_H W2) (ms_mem ms2) a = aview segs (w_H W2) mem2 a).
  { intros a Ha Hn. unfold dkg_nf in Hn. change (fs_frame_bytes ONANN_CID / 8) with 128 in Hn.
    change (fs_frame_bytes ONANN_CID) with 1024 in Hn.
    rewrite (KP3 a Ha ltac:(intros E'; apply Hn; left; right; right; exact E')).
    apply KM; [exact Ha | | |].
    - intros Hz. apply Hn. left. unfold ot_Z1 in Hz. destruct Hz as [Hz | Hz]; [right; left | left]; lia.
    - intros Hz. apply Hn. left. right. left. exact Hz.
    - intros Hz. apply Hn. right. exact Hz. }
  assert (GALL : forall a, apresent (w_H W2) mem2 a -> apresent (w_H W2) (ms_mem ms2) a)
    by (intros a Ha; exact (apresent_grows _ _ _ a HG2 (GM a Ha))).
  eapply (paj_ret_at (fx := fx) (PL := PL_transport) (PI := PI_transport) W2 E3 ot_ss_end ms2 md3 _
    HS2 eq_refl ltac:(clear; vm_compute; reflexivity)).
  intros mat3.
  set (md4 := with_vm_backing (m_vm_lazy md3) mat3 md3).
  pose proof (ajournal_gx_materialize segs B LAWS transport_segs_low _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ mat3 HJ3)
    as HJ4.
  fold md4 in HJ4. clearbody md4.
  (* the registers at the ret *)
  assert (R1e : YK11.getr (ms_regs ms2) 1 = YK11.getr regs 1).
  { ot_regv HS2. cbn [sv_denot]. rewrite Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity. }
  assert (HP : aregs_preserved regs (ms_regs ms2)).
  { intros r Hr. unfold acallee_saved in Hr.
    assert (Hr' : r = 2 \/ r = 3 \/ r = 4 \/ r = 8 \/ r = 9 \/ r = 18 \/ r = 19 \/ r = 20 \/ r = 21 \/ r = 22 \/
      r = 23 \/ r = 24 \/ r = 25 \/ r = 26 \/ r = 27) by lia.
    clear Hr.
    destruct Hr' as [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | ->]]]]]]]]]]]]]];
      ot_regv HS2; cbn [sv_denot]; rewrite Z.add_0_r, Z_to_bv_bv_unsigned.
    all: first
      [ reflexivity
      | transitivity (YK11.getr regsM 3); [apply ot_ew_reg; reflexivity | exact M3]
      | transitivity (YK11.getr regsM 4); [apply ot_ew_reg; reflexivity | exact M4]
      | transitivity (YK11.getr regsM 8); [apply ot_ew_reg; reflexivity|];
        rewrite M8; unfold w64, spZ; apply Z_to_bv_bv_unsigned ]. }
  assert (Hpc : v_jalr (YK11.getr (ms_regs ms2) 1) 0 = YK11.getr regs 1) by (rewrite R1e; exact Hret).
  assert (Eab' : ablocks B ly2 (stack_free_state ONANN_CID pos S2) = ablocks B ly2 S2)
    by (unfold ablocks; rewrite blocks_stack_free_state; reflexivity).
  unfold transport_onann_post, transport_cg_post.
  exists ly2, (stack_free_state ONANN_CID pos S2), (ms_regs ms2), (ms_mem ms2), md4, e.
  split; [rewrite Hpc; reflexivity|].
  split; [exact He|].
  split; [exact HJ4|].
  split; [exact HP|].
  split; [exact (can_sf_frames ONANN_CID pos S2 (frames Sc) Hfrs)|].
  split; [rewrite Eab'; exact Hperm|].
  split.
  { (* the cut's acall_kept_g, over arel's bytes (the own frame, its shadow, its flag byte, the call's scratch) *)
    apply (dk_kept_nfz_gw segs B LAWS transport_segs_low TG.G_HARNESS lyc Sc ly2 S2 W memc mdc W2 mem2 md2 mem2
      (ms_mem ms2) (spZ regs - ONANN_STK) (spZ regs) ONANN_CID pos F FL (onann_wr Bw b)
      (fun a => dkg_nf ONANN_CID F FL a \/ (sp1 - ESTACK <= a < sp1))
      HGX HARc HAR2 Hfrs Hbl ELF EF EFL FFL ltac:(lia) ltac:(lia)); [| exact HK | exact KALL | exact GALL].
    intros a [Hn | Hw]; [right; left; exact Hn | left; lia]. }
  split; [unfold stack_free_state; apply (mo_le_set_fs_r MT MTF); exact Hmo|].
  (* the world relation at Bw': no byte of G is a byte arel wrote *)
  split; [|exact Hgf2].
  apply (tw_kept_GA (aview segs (w_H W2) mem2)); [exact HTW2|].
  intros b0 n i Hbn Hi.
  assert (HG : inG TG.G_HARNESS (b0 + i))
    by (unfold inG; apply Exists_exists; exists (b0, n); split; [exact Hbn | unfold in_zr; cbn [fst snd]; lia]).
  destruct (HGX _ HG) as [HiG _].
  pose proof (transport_segs_low _ HiG) as Hl. unfold kLowMemEnd in Hl.
  apply KALL; [lia|]. intros [Hn | Hw]; [exact (N2 _ Hn HiG) | lia].
Qed.

(* ------------------------------------------------------------------ *)
(* 3. nrel, +0x764 .. +0x788, and fnrel, +0x73c .. +0x760              *)
(* ------------------------------------------------------------------ *)

Lemma ot_nrel : @onann_arel_at fx rc B MT -> @onann_nrel_at fx rc B MT.
Proof.
intros AREL. unfold onann_nrel_at.
intros LAWS0 CALLEES STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs fp buf now b fj TF Bw Bw' pos sp1 F
  ly2 S2 W2 mem2 md2 e regs2 HFIX HCUR HREGS.
pose proof LAWS0 as (_ & _ & _ & _ & _ & _ & _ & LAWS & _ & _ & _ & _ & FFL & HGX & _).
pose proof HFIX as (HJ0 & _ & _ & _ & _ & _ & _ & _ & _ & Hlo & Hhi & _ & _ & _ & _ & _ & _ & _ & _ & _ &
  _ & _ & _ & _ & _ & EF & HF0 & HF64 & HFc & HFapp).
pose proof HCUR as ((HJ1 & He & Hfrs & Hperm & ELF & Hmo & HK & Hsaved & HFLw) & HTW2 & Hgf2).
pose proof HREGS as ((R2 & R3 & R4 & R8 & R9 & R18 & R19) & R23).
unfold ONANN_FBYTES in HFc, HFapp.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (HFc47 : F + 1024 <= 2 ^ 47) by lia.
destruct (ot_fsh F HF0 HF64 HFc47) as (HF8 & DF & HF8b & M8).
pose proof HJ0 as (_ & _ & (memS & HJi & _) & _). rewrite !Z.add_0_r in HJi.
pose proof HJi as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hstk & _).
pose proof Hstk as (_ & _ & Hceil & Hslo & Hshi & H47 & _).
clear HJi memS.
assert (HBS : 4240 <= ONANN_STK).
{ unfold ONANN_STK, ONANN_FRAME, ONANN_ALIGN.
  lazymatch goal with |- _ <= _ + _ + Z.max ?a ?b =>
    pose proof (Z.le_max_l a b) as Hm0; assert (Ha : a = 4096) by reflexivity end.
  lia. }
pose proof (ajournal_gx_AR segs B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ0) as HARc.
pose proof (ajournal_gx_AR segs B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ1) as HAR2.
assert (Hin : In (ONANN_CID, pos) (frames S2)) by (rewrite Hfrs; left; reflexivity).
assert (EFA : frame_addr ly2 ONANN_CID pos = F) by (rewrite EF; unfold frame_addr; rewrite ELF; reflexivity).
destruct (al_frames _ _ LAWS _ _ _ _ _ ONANN_CID pos HAR2 Hin) as (_ & _ & _ & HFsh).
change (fs_frame_bytes ONANN_CID / 8) with 128 in HFsh. rewrite EFA in HFsh.
assert (ESH : shadow_addr F = SHADOW_OFF + F / 8) by reflexivity.
rewrite ESH in HFsh.
(* +0x764 .. +0x788: n's shadow bytes 42 .. 50 := 0xf8, to +0x78c *)
pose proof (ot_entry_sh W2 regs2 mem2 F ONANN_NREL 42 51 R19 HF0 HF64 HFc47 ltac:(lia) ltac:(lia) ltac:(lia)
  ltac:(vm_compute; reflexivity) ltac:(intros i Hi; exact (proj1 (HFsh i ltac:(lia))))) as HS.
change (mkSS ONANN_NREL sr_atoms [ot_rg_sh 42 51] None ot_facts_sh) with ss_otn in HS.
set (E0 := Eimg (PI := PI_transport) (Ereg regs2 [])) in HS.
assert (HEI : img_env VAL A_LIM E0) by (unfold E0; apply Eimg_env).
assert (EE : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E0 n = YK11.getr regs2 r)
  by (intros n r Hn; unfold E0; apply can_ew_Eimg_Ereg_nat; exact Hn).
assert (U19 : bv_unsigned (ew E0 19) = SHADOW_OFF + F / 8)
  by (rewrite (EE 19%nat 19%bv eq_refl), R19; unfold w64; apply unsigned_lit_small; unfold SHADOW_OFF; lia).
assert (SHOK : sh_ok segs OT_Bx (@nil shent) E0 (mrestrict (w_H W2) mem2)) by constructor.
pose proof (@paj_run_to_x fx rc tfib_sink_head transport_listing PL_transport PI_transport B LAWS TG.G_HARNESS HGX 0 [])
  as RUNTO.
paj_run_to_tok RUNTO HS HJ1 SHOK OT_B0 ONANN_AREL.
{ lazymatch goal with |- awr_ok_x ?Ex ?rs ?Gx ?XO ?OUT ?stk ?sp0q ?fp ?b0 ?bc ?lyq ?ownq =>
    let rs' := eval vm_compute in rs in change (awr_ok_x Ex rs' Gx XO OUT stk sp0q fp b0 bc lyq ownq) end.
  eapply awr_ok_x_cons_own with (cid := ONANN_CID); [left; reflexivity | |].
  - intros a Ha. cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha. rewrite U19 in Ha.
    right. unfold in_zr. cbn [fst snd]. rewrite EFA, ESH. change (fs_frame_bytes ONANN_CID / 8) with 128. lia.
  - apply awr_ok_x_nil. }
set (md3 := with_vm_backing (m_vm_lazy md2) mat md2) in *. clearbody md3. clear mat.
assert (KR : forall a, 0 <= a < 2 ^ 64 -> ~ (SHADOW_OFF + F / 8 + 42 <= a < SHADOW_OFF + F / 8 + 51) ->
  aview segs (w_H W2) (ms_mem ms) a = aview segs (w_H W2) mem2 a).
{ intros a Ha Hn.
  apply (kept_of_frame _ _ _ _ _ (fun x => SHADOW_OFF + F / 8 + 42 <= x < SHADOW_OFF + F / 8 + 51) HFr);
    [| exact Ha | exact Hn].
  intros b0 wlo whi x Hiw Hx. cbv beta. ot_win Hiw Hx ltac:(rewrite ?U19 in Hx; lia). }
assert (GR : forall a, apresent (w_H W2) mem2 a -> apresent (w_H W2) (ms_mem ms) a)
  by (intros a Ha; exact (apresent_grows _ _ _ a HG Ha)).
clear HF HFr HG.
lazymatch type of HS with st_ok_pi _ _ ?EF _ (restrict _ ?mf) => set (E5 := EF) in HS; rename mf into msF end.
assert (E5lo : forall n, (n < 1024)%nat -> ew E5 n = ew E0 n)
  by (intros n Hn; unfold E5; rewrite ?ew_ewset_other by lia; reflexivity).
(* the registers the release reads, at the cut *)
ot_kreg HS E5lo EE (2%bv : bv 5) 2%nat R2 X2. ot_kreg HS E5lo EE (3%bv : bv 5) 3%nat R3 X3.
ot_kreg HS E5lo EE (4%bv : bv 5) 4%nat R4 X4. ot_kreg HS E5lo EE (8%bv : bv 5) 8%nat R8 X8.
ot_kreg HS E5lo EE (9%bv : bv 5) 9%nat R9 X9. ot_kreg HS E5lo EE (18%bv : bv 5) 18%nat R18 X18.
ot_kreg HS E5lo EE (19%bv : bv 5) 19%nat R19 X19. ot_kreg HS E5lo EE (23%bv : bv 5) 23%nat R23 X23.
destruct (ot_kept_move lyc Sc W memc mdc ly2 S2 W2 mem2 md2 (ms_mem msF) (spZ regs - ONANN_STK) (spZ regs) pos F
  (onann_wr Bw b) (fun x => SHADOW_OFF + F / 8 + 42 <= x < SHADOW_OFF + F / 8 + 51) regs Bw' LAWS FFL HGX HARc HAR2
  Hfrs Hperm ELF EF HF0 HF64 HFc HFapp ltac:(lia) ltac:(lia) ltac:(intros a Ha; cbv beta in Ha; lia) KR GR HK Hsaved
  HFLw HTW2)
  as (K3 & SV3 & FL3 & TW3).
(* the cut at +0x78c *)
pmkst HS.
lazymatch goal with |- SRr ?sg ?Wx (mkCfg (@YK11.mkst _ ?rg _ ?mm ?rom) ?mdx) ?Q =>
  change (SRr sg Wx (mkCfg (@YK11.mkst fx rg (Z_to_bv 64 (BASE + ONANN_AREL)) mm rom) mdx) Q) end.
apply (AREL LAWS0 CALLEES STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs fp buf now b fj TF Bw Bw' pos sp1
  F ly2 S2 W2 (ms_mem msF) md3 e (ms_regs msF) HFIX).
- refine (conj (conj HJ1 (conj He (conj Hfrs (conj Hperm (conj ELF (conj Hmo (conj K3 (conj SV3 FL3)))))))) (conj TW3 Hgf2)).
- exact (conj (conj X2 (conj X3 (conj X4 (conj X8 (conj X9 (conj X18 X19)))))) X23).
Qed.

Lemma ot_fnrel : @onann_nrel_at fx rc B MT -> @onann_fnrel_at fx rc B MT.
Proof.
intros NREL. unfold onann_fnrel_at.
intros LAWS0 CALLEES STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs fp buf now b fj TF Bw Bw' pos sp1 F
  ly2 S2 W2 mem2 md2 e regs2 HFIX HCUR HREGS.
pose proof LAWS0 as (_ & _ & _ & _ & _ & _ & _ & LAWS & _ & _ & _ & _ & FFL & HGX & _).
pose proof HFIX as (HJ0 & _ & _ & _ & _ & _ & _ & _ & _ & Hlo & Hhi & _ & _ & _ & _ & _ & _ & _ & _ & _ &
  _ & _ & _ & _ & _ & EF & HF0 & HF64 & HFc & HFapp).
pose proof HCUR as ((HJ1 & He & Hfrs & Hperm & ELF & Hmo & HK & Hsaved & HFLw) & HTW2 & Hgf2).
pose proof HREGS as ((R2 & R3 & R4 & R8 & R9 & R18 & R19) & R23).
unfold ONANN_FBYTES in HFc, HFapp.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (HFc47 : F + 1024 <= 2 ^ 47) by lia.
destruct (ot_fsh F HF0 HF64 HFc47) as (HF8 & DF & HF8b & M8).
pose proof HJ0 as (_ & _ & (memS & HJi & _) & _). rewrite !Z.add_0_r in HJi.
pose proof HJi as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hstk & _).
pose proof Hstk as (_ & _ & Hceil & Hslo & Hshi & H47 & _).
clear HJi memS.
assert (HBS : 4240 <= ONANN_STK).
{ unfold ONANN_STK, ONANN_FRAME, ONANN_ALIGN.
  lazymatch goal with |- _ <= _ + _ + Z.max ?a ?b =>
    pose proof (Z.le_max_l a b) as Hm0; assert (Ha : a = 4096) by reflexivity end.
  lia. }
pose proof (ajournal_gx_AR segs B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ0) as HARc.
pose proof (ajournal_gx_AR segs B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ1) as HAR2.
assert (Hin : In (ONANN_CID, pos) (frames S2)) by (rewrite Hfrs; left; reflexivity).
assert (EFA : frame_addr ly2 ONANN_CID pos = F) by (rewrite EF; unfold frame_addr; rewrite ELF; reflexivity).
destruct (al_frames _ _ LAWS _ _ _ _ _ ONANN_CID pos HAR2 Hin) as (_ & _ & _ & HFsh).
change (fs_frame_bytes ONANN_CID / 8) with 128 in HFsh. rewrite EFA in HFsh.
assert (ESH : shadow_addr F = SHADOW_OFF + F / 8) by reflexivity.
rewrite ESH in HFsh.
(* +0x73c .. +0x760: fn's shadow bytes 56 .. 64 := 0xf8, to +0x764 *)
pose proof (ot_entry_sh W2 regs2 mem2 F ONANN_FNREL 56 65 R19 HF0 HF64 HFc47 ltac:(lia) ltac:(lia) ltac:(lia)
  ltac:(vm_compute; reflexivity) ltac:(intros i Hi; exact (proj1 (HFsh i ltac:(lia))))) as HS.
change (mkSS ONANN_FNREL sr_atoms [ot_rg_sh 56 65] None ot_facts_sh) with ss_otfn in HS.
set (E0 := Eimg (PI := PI_transport) (Ereg regs2 [])) in HS.
assert (HEI : img_env VAL A_LIM E0) by (unfold E0; apply Eimg_env).
assert (EE : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E0 n = YK11.getr regs2 r)
  by (intros n r Hn; unfold E0; apply can_ew_Eimg_Ereg_nat; exact Hn).
assert (U19 : bv_unsigned (ew E0 19) = SHADOW_OFF + F / 8)
  by (rewrite (EE 19%nat 19%bv eq_refl), R19; unfold w64; apply unsigned_lit_small; unfold SHADOW_OFF; lia).
assert (SHOK : sh_ok segs OT_Bx (@nil shent) E0 (mrestrict (w_H W2) mem2)) by constructor.
pose proof (@paj_run_to_x fx rc tfib_sink_head transport_listing PL_transport PI_transport B LAWS TG.G_HARNESS HGX 0 [])
  as RUNTO.
paj_run_to_tok RUNTO HS HJ1 SHOK OT_B0 ONANN_NREL.
{ lazymatch goal with |- awr_ok_x ?Ex ?rs ?Gx ?XO ?OUT ?stk ?sp0q ?fp ?b0 ?bc ?lyq ?ownq =>
    let rs' := eval vm_compute in rs in change (awr_ok_x Ex rs' Gx XO OUT stk sp0q fp b0 bc lyq ownq) end.
  eapply awr_ok_x_cons_own with (cid := ONANN_CID); [left; reflexivity | |].
  - intros a Ha. cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha. rewrite U19 in Ha.
    right. unfold in_zr. cbn [fst snd]. rewrite EFA, ESH. change (fs_frame_bytes ONANN_CID / 8) with 128. lia.
  - apply awr_ok_x_nil. }
set (md3 := with_vm_backing (m_vm_lazy md2) mat md2) in *. clearbody md3. clear mat.
assert (KR : forall a, 0 <= a < 2 ^ 64 -> ~ (SHADOW_OFF + F / 8 + 56 <= a < SHADOW_OFF + F / 8 + 65) ->
  aview segs (w_H W2) (ms_mem ms) a = aview segs (w_H W2) mem2 a).
{ intros a Ha Hn.
  apply (kept_of_frame _ _ _ _ _ (fun x => SHADOW_OFF + F / 8 + 56 <= x < SHADOW_OFF + F / 8 + 65) HFr);
    [| exact Ha | exact Hn].
  intros b0 wlo whi x Hiw Hx. cbv beta. ot_win Hiw Hx ltac:(rewrite ?U19 in Hx; lia). }
assert (GR : forall a, apresent (w_H W2) mem2 a -> apresent (w_H W2) (ms_mem ms) a)
  by (intros a Ha; exact (apresent_grows _ _ _ a HG Ha)).
clear HF HFr HG.
lazymatch type of HS with st_ok_pi _ _ ?EF _ (restrict _ ?mf) => set (E5 := EF) in HS; rename mf into msF end.
assert (E5lo : forall n, (n < 1024)%nat -> ew E5 n = ew E0 n)
  by (intros n Hn; unfold E5; rewrite ?ew_ewset_other by lia; reflexivity).
ot_kreg HS E5lo EE (2%bv : bv 5) 2%nat R2 X2. ot_kreg HS E5lo EE (3%bv : bv 5) 3%nat R3 X3.
ot_kreg HS E5lo EE (4%bv : bv 5) 4%nat R4 X4. ot_kreg HS E5lo EE (8%bv : bv 5) 8%nat R8 X8.
ot_kreg HS E5lo EE (9%bv : bv 5) 9%nat R9 X9. ot_kreg HS E5lo EE (18%bv : bv 5) 18%nat R18 X18.
ot_kreg HS E5lo EE (19%bv : bv 5) 19%nat R19 X19. ot_kreg HS E5lo EE (23%bv : bv 5) 23%nat R23 X23.
destruct (ot_kept_move lyc Sc W memc mdc ly2 S2 W2 mem2 md2 (ms_mem msF) (spZ regs - ONANN_STK) (spZ regs) pos F
  (onann_wr Bw b) (fun x => SHADOW_OFF + F / 8 + 56 <= x < SHADOW_OFF + F / 8 + 65) regs Bw' LAWS FFL HGX HARc HAR2
  Hfrs Hperm ELF EF HF0 HF64 HFc HFapp ltac:(lia) ltac:(lia) ltac:(intros a Ha; cbv beta in Ha; lia) KR GR HK Hsaved
  HFLw HTW2)
  as (K3 & SV3 & FL3 & TW3).
(* the cut at +0x764 *)
pmkst HS.
lazymatch goal with |- SRr ?sg ?Wx (mkCfg (@YK11.mkst _ ?rg _ ?mm ?rom) ?mdx) ?Q =>
  change (SRr sg Wx (mkCfg (@YK11.mkst fx rg (Z_to_bv 64 (BASE + ONANN_NREL)) mm rom) mdx) Q) end.
apply (NREL LAWS0 CALLEES STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs fp buf now b fj TF Bw Bw' pos sp1
  F ly2 S2 W2 (ms_mem msF) md3 e (ms_regs msF) HFIX).
- refine (conj (conj HJ1 (conj He (conj Hfrs (conj Hperm (conj ELF (conj Hmo (conj K3 (conj SV3 FL3)))))))) (conj TW3 Hgf2)).
- exact (conj (conj X2 (conj X3 (conj X4 (conj X8 (conj X9 (conj X18 X19)))))) X23).
Qed.

Lemma ot_tail : @onann_tail_stmt fx rc B MT.
Proof.
pose proof ot_arel as AREL. pose proof (ot_nrel AREL) as NREL.
exact (conj AREL (conj NREL (ot_fnrel NREL))).
Qed.

End tail.

(* The release tail of the walk of on_announce (OnannCut.v onann_tail_stmt), at every machine, run ceiling, record and
   meter. *)
Theorem onann_piece_tail : forall fx rc B MT, @onann_tail_stmt fx rc B MT.
Proof. intros fx rc B MT. exact (@ot_tail fx rc B MT). Qed.
