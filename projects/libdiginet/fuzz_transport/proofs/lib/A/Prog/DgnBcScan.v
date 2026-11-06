(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: restates text of projects/cgif/cgif_file_fuzzer/proofs/lib/YCbq.v:528-543, 616-634;
   projects/cgif/cgif_rgb_fuzzer/proofs/lib/YC05.v:41-45, 208-214, 230-234, for libreac/fuzz_identity's asan-ubsan build
   (lib/B). The same text also appears in projects/cgif/cgif_file_fuzzer/proofs/lib/YCbo.v:420-423, 430-444, 447-448,
   453-455, 470-475, 477-486, 489-491, 502-505, 511-514, 1255-1258. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_identity/lib/B/Prog/reac_box_name_seg_rel.v, with its module paths, module names and numbers changed; 274 of its 316 lines of code are new or changed and 1882 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libdiginet/fuzz_transport/lib/A/Prog/DgnBcRel.v; 582 of its 621 lines of code are new or changed and 277 lines of the source are left out. *)
(* DgnBcScan: Lemma bc_scan : bc_rel_stmt -> bc_scan_stmt (lib/A/Prog/DgnBcCut.v), the prefix scan of
   diginet_body_check (fuzz_decode.asan 0x826dc = dgndec_sigma DD_diginet_body_check), offsets +0x1ec .. +0x294 and
   +0x404 of the listing lib/A/Prog/DgnDecodeList.v, up to the release at +0x298 (BC_REL, the premise).
   The code writes no memory and calls nothing:
     +0x1ec .. +0x1f4  a0 = 4, s4 = the word at s1 + 16 (len), `bltu s4,a0` to +0x294;
     +0x1f8 .. +0x208  a1 = s3 + 1, s4 = len - 3, a2 = 240, a3 = 19, a4 = 112;
     +0x20c .. +0x258  turn i (s3 = body + i, a1 = body + i + 1, s4 = len - 3 - i): the instrumented check of the byte
                       at s3, the load of body[i] and `bne a0,a2` to +0x25c; the check of s3 + 1, body[i + 1] and
                       `bne a0,a3` to +0x25c; the check of s3 + 3, body[i + 3] and `beq a0,a4` to +0x404
                       (`li a0,-10`, `j +0x298`);
     +0x25c .. +0x268  s3, a1 one up, s4 one down, `bnez s4` to +0x20c; else +0x26c `j +0x294`;
     +0x294            `li a0,0`, then +0x298.
   How it is proved. Three segments run on the PA engine with its token shadow checks (lib/A/Prog/PaShadow.v), each
   from a fresh symbolic state whose regions are read-only, so each run leaves the memory as it was
   (frame_of_read_only) and changes only the model's materialized part (ajournal_materialize keeps the journal):
     bcs_head  +0x1ec: the 8-byte slot at s1 + 16 holding len (atom 32), split on `bltu`;
     bcs_body  +0x20c: the three body bytes as a read-only region at a1 (atoms 32, 33, 34), the shadow entry of the
               four bytes at s3 (range_addressable of the body's heap block, lib/Reusable/YCbq.v
               range_addressable_of_block), so the engine decides the three checks; split on the byte compares;
     bcs_bump  +0x25c: split on `bnez s4`.
   The loop is an induction on len - 3 - i (bcs_loop) with the invariant bcs_inv at +0x20c and sys_hit bb j = false
   for j < i; at the release a0 is body_check bb by body_check_spec, system_at_true and system_at_false. *)
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s YK0o.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import YN3v YI04 YI00 YI09.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq YG0p YG0s YC5d.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import YM05 YImgTop.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require YI16 YI5b YI5c.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import PaTable PaSym PaStep PaRun PaShadow PaJournal.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import
DgnTransportSyms DgnTransportList DgnTransportAddr DgnTransportPa DgnTransportImg DgnTransportPaLib DgnTransportCJ.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A Require Import AB1v Img0.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A Require AE2k AsanCells.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Spec Require Import DgnSpec DgnLib.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import DgnTransportCg diginet_body_check_cg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require diginet_msg_next_cg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import DgnBcCut.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.
Module YK11 := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YK11.
#[global] Remove Hints OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5b.src0_sink_head
  OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5c.src0_sink
  OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5c.src0_sink_laws : typeclass_instances.

(* ------------------------------------------------------------------ *)
(* The symbolic states                                                 *)
(* ------------------------------------------------------------------ *)

(* Offsets of the scan from the listing's base. *)
Definition SC_AT (k : Z) : Z := AF_diginet_body_check + k.
(* s9 holds the shadow base; the shadow span the token engine checks against. *)
Definition bcs_Bx : sv := SOff 25 0.
Definition bcs_Bspan : Z * Z := (SHADOW_OFF, SHADOW_OFF + 2 ^ 44 - 1).
(* The shadow entry of turn i: the four bytes at s3 = body + i. *)
Definition bcs_SH : list shent := [mkSHE 19 0 4].
(* 2 ^ 47 - 4: the atom bound of a scan pointer p (s3) and of a1 = p + 1. The shadow entry of a turn covers
   [p, p + 4) and the engine checks its shadow addresses inside bcs_Bspan, which holds for p + 3 <= 2 ^ 47 - 1.
   Every body trans_src_ok places has body + len <= 2 ^ 47 - 1 (decode_rd_ok's amem_range), a machine-stack body
   included (S11-DECISIONS (b)), so a turn's p + 1 <= 2 ^ 47 - 4. *)
Definition bcs_PTRHI : Z := 140737488355324.
Definition bcs_PTR : afact := mkAF 4096 bcs_PTRHI 0.
Definition bcs_G : facts := mkFacts [(25%nat, mkAF SHADOW_OFF SHADOW_OFF 0); (19%nat, bcs_PTR); (11%nat, bcs_PTR);
  (32%nat, mkAF 0 255 0); (33%nat, mkAF 0 255 0); (34%nat, mkAF 0 255 0)] [] [].
(* Turn i at +0x20c: body[i], body[i + 1], body[i + 3] at a1 - 1, a1, a1 + 2, as atoms 32, 33, 34. *)
Definition bcs_rg : YP09.region := YP09.mkRegion (Some 11%nat) (-1) 3 0 0
  [YP09.mkChunk (-1) (CVal 1 (SOff 32 0)); YP09.mkChunk 0 (CVal 1 (SOff 33 0)); YP09.mkChunk 2 (CVal 1 (SOff 34 0))].
Definition bcs_ss : sstate := mkSS (SC_AT 0x20c) sr_atoms [bcs_rg] None bcs_G.
(* The head at +0x1ec: the slot s1 + 16 holding len, as atom 32. *)
Definition bch_rg : YP09.region := YP09.mkRegion (Some 9%nat) 16 24 0 0 [YP09.mkChunk 16 (CVal 8 (SOff 32 0))].
Definition bch_ss : sstate := mkSS (SC_AT 0x1ec) sr_atoms [bch_rg] None (mkFacts [] [] []).
(* The back edge at +0x25c. *)
Definition bcb_ss : sstate := mkSS (SC_AT 0x25c) sr_atoms [] None (mkFacts [] [] []).
(* Registers a run keeps: the ones the release reads, and the loop's own. *)
Definition kp_rel : list (bv 5) := [2%bv; 3%bv; 4%bv; 8%bv; 9%bv; 23%bv; 24%bv].
Definition kp_lp : list (bv 5) := [11%bv; 12%bv; 13%bv; 14%bv; 19%bv; 20%bv; 25%bv].
Definition kp_bp : list (bv 5) := [12%bv; 13%bv; 14%bv; 25%bv].
Definition kp_hd : list (bv 5) := [19%bv; 25%bv].

Ltac bcs_kin := unfold kp_rel, kp_lp, kp_bp, kp_hd; cbn [In]; repeat (first [left; reflexivity | right]).

(* ------------------------------------------------------------------ *)
(* Environments, bytes, the model of body_check                        *)
(* ------------------------------------------------------------------ *)

Lemma bcs_agree_ew : forall E0 E n, env_agree 512 E0 E -> (n < 512)%nat -> ew E n = ew E0 n.
Proof. intros E0 E n [H _] Hn. exact (H n Hn). Qed.

Lemma bcs_agree_extK : forall E0 E K ws, (512 <= K)%nat -> env_agree 512 E0 E -> env_agree 512 E0 (extK E K ws).
Proof.
  intros E0 E K ws HK [H1 H2]. destruct (env_agree_extK E K ws) as [A1 A2].
  split; [intros n Hn; rewrite (A1 n ltac:(lia)); exact (H1 n Hn) | rewrite A2; exact H2].
Qed.

Lemma bcs_U : forall E0 E n v, env_agree 512 E0 E -> (n < 512)%nat -> ew E0 n = w64 v -> 0 <= v < 2 ^ 64 ->
  U E (SOff n 0) = v.
Proof. intros E0 E n v HA Hn H Hv. apply U_atom; [rewrite (bcs_agree_ew E0 E n HA Hn); exact H | exact Hv]. Qed.

Lemma bcs_Uoff : forall E0 E n v c, env_agree 512 E0 E -> (n < 512)%nat -> ew E0 n = w64 v -> 0 <= v < 2 ^ 64 ->
  0 <= v + c < 2 ^ 64 -> U E (SOff n c) = v + c.
Proof.
  intros E0 E n v c HA Hn H Hv Hvc.
  apply U_atom_off; [rewrite (bcs_agree_ew E0 E n HA Hn); exact H | exact Hv | exact Hvc].
Qed.

Lemma bcs_den : forall E0 E n v c, env_agree 512 E0 E -> (n < 512)%nat -> ew E0 n = w64 v -> 0 <= v < 2 ^ 64 ->
  sv_denot E (SOff n c) = w64 (v + c).
Proof.
  intros E0 E n v c HA Hn H Hv. cbn [sv_denot]. rewrite (bcs_agree_ew E0 E n HA Hn), H.
  unfold w64. rewrite unsigned_lit_small by lia. reflexivity.
Qed.

Lemma bcs_rel_kept : forall regs r1 r2 sp1 F, bc_regs_rel regs r1 sp1 F ->
  (forall x, In x kp_rel -> YK11.getr r2 x = YK11.getr r1 x) -> bc_regs_rel regs r2 sp1 F.
Proof.
  intros regs r1 r2 sp1 F (H2 & H3 & H4 & H8 & H9 & H23 & H24) HK. unfold bc_regs_rel.
  split; [rewrite HK; [exact H2 | bcs_kin]|].
  split; [rewrite HK; [exact H3 | bcs_kin]|].
  split; [rewrite HK; [exact H4 | bcs_kin]|].
  split; [rewrite HK; [exact H8 | bcs_kin]|].
  split; [rewrite HK; [exact H9 | bcs_kin]|].
  split; [rewrite HK; [exact H23 | bcs_kin]|].
  rewrite HK; [exact H24 | bcs_kin].
Qed.

Lemma bcs_nth_bz : forall (l : list byte) j, nth j (map bz l) 0 = at8 l j.
Proof. intros l j. unfold at8. rewrite <- (map_nth bz l (b8 0) j). reflexivity. Qed.

Lemma bcs_hit0 : forall bb i, at8 bb i <> 240 -> sys_hit bb i = false.
Proof. intros bb i H. unfold sys_hit. apply Z.eqb_neq in H. rewrite H. reflexivity. Qed.

Lemma bcs_hit1 : forall bb i, at8 bb (S i) <> 19 -> sys_hit bb i = false.
Proof. intros bb i H. unfold sys_hit. apply Z.eqb_neq in H. rewrite H, andb_false_r. reflexivity. Qed.

Lemma bcs_hit3 : forall bb i, at8 bb (S (S (S i))) <> 112 -> sys_hit bb i = false.
Proof. intros bb i H. unfold sys_hit. apply Z.eqb_neq in H. rewrite H, andb_false_r. reflexivity. Qed.

Lemma bcs_hit_true : forall bb i, at8 bb i = 240 -> at8 bb (S i) = 19 -> at8 bb (S (S (S i))) = 112 ->
  sys_hit bb i = true.
Proof. intros bb i H0 H1 H3. unfold sys_hit. rewrite H0, H1, H3. reflexivity. Qed.

Lemma bcs_bc0 : forall bb, system_at bb = false -> body_check bb = 0.
Proof. intros bb H. rewrite body_check_spec, H. reflexivity. Qed.

(* ------------------------------------------------------------------ *)
(* One run of the engine over read-only regions                        *)
(* ------------------------------------------------------------------ *)

Section run. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Local Abbreviation segs := tfibsegs.
Local Abbreviation VAL := (@pa_val _ transport_listing PI_transport).

(* The run writes no memory (its regions are read-only), so the memory after it is the memory before; the model
   after it is the model before with its materialized part replaced. *)
Lemma bcs_run : forall (Bx : sv) (Bspan : Z * Z) (SH : list shent) (W : world segs) (E : env) (ss : sstate)
    (ms : machine_state) (md : Model) (K : nat) (stop : Z) (st' : shst) (r : ptrun_status tsym)
    (Q : world segs -> config -> Prop),
  (A_LIM <= K)%nat ->
  img_env VAL A_LIM E ->
  st_ok_pi segs VAL E ss (restrict (w_H W) ms) ->
  sh_ok segs Bx SH E (mrestrict (w_H W) (ms_mem ms)) ->
  sh_static_ok K Bx Bspan SH (ss_facts ss) (ss_mem ss) = true ->
  sym_run_toN_pi_tok transport_tpi transport_tw K Bx Bspan SH FUEL stop ss = (st', r) ->
  match r with PTS_call _ => False | PTS_ecall => False | _ => True end ->
  Forall (ob_holds segs Bx E (mrestrict (w_H W) (ms_mem ms))) (sh_obls st') ->
  rs_read_only (ss_mem ss) = true ->
  (forall ws ms' mat,
     length ws = sh_j st' ->
     img_env VAL A_LIM (extK E K ws) ->
     st_ok_pi segs VAL (extK E K ws) (sh_ss st') (restrict (w_H W) ms') ->
     sh_ok segs Bx SH (extK E K ws) (mrestrict (w_H W) (ms_mem ms')) ->
     ms_mem ms' = ms_mem ms ->
     SRr segs W (mkCfg ms' (with_vm_backing (m_vm_lazy md) mat md)) Q) ->
  SRr segs W (mkCfg ms md) Q.
Proof.
  intros Bx Bspan SH W E ss ms md K stop st' r Q HK HE HS HSH Hchk Hrun Hnc Hobl Hro HKQ.
  assert (Hrun' : sym_run_toN_pi_tok (ptree_of_list transport_listing) (tw_of 0 transport_listing)
                    K Bx Bspan SH FUEL stop ss = (st', r))
    by (rewrite (@pl_tw_eq transport_listing PL_transport); exact Hrun).
  destruct (sym_run_to_pi_tok_sound tsym _ _ VAL _ transport_listing
     (pa_fetch_ok (PI := PI_transport)) (@pa_cert _ transport_listing PI_transport)
     (@pa_B_ok _ transport_listing PI_transport)
     A_LIM A_LIM_text (@pl_lim transport_listing PL_transport) (@pl_len transport_listing PL_transport)
     K Bx Bspan SH HK FUEL stop E ss (restrict (w_H W) ms) st' r HE HS HSH Hchk Hrun' Hobl)
   as (ws & msr' & Hlen & Hms & HE' & HP & Hsh' & _ & Hfr).
  apply (SRr_msteps segs (@pa_wx _ transport_listing PI_transport) W ms msr' md Q Hms).
  intros model' Hsame Hcl.
  rewrite (same_but_materialized_wvb md model' Hsame).
  pose proof (restrict_unrestrict_clean (w_H W) (ms_mem ms) msr' Hcl) as Hrr.
  pose proof (mrestrict_unrestrict_mem (w_H W) (ms_mem ms) msr' Hcl) as Hmm.
  assert (Hmem : ms_mem (unrestrict (w_H W) (ms_mem ms) msr') = ms_mem ms).
  { eapply frame_of_read_only; [exact Hro|].
    cbn [unrestrict ms_mem]. apply frame_of_unrestrict.
    cbn [restrict ms_mem] in Hfr. exact Hfr. }
  apply (HKQ ws (unrestrict (w_H W) (ms_mem ms) msr') (m_vm_materialized model') Hlen HE').
  - rewrite Hrr. destruct r as [ | | s | why]; cbn [ptok_post] in HP;
    [exact HP | destruct HP | destruct Hnc | exact HP].
  - rewrite Hmm. exact Hsh'.
  - exact Hmem.
Qed.

End run.

(* One run to the pc stop, or to the next branch the engine cannot decide. *)
Ltac bcs_step SH stop :=
  lazymatch goal with
  | HS : st_ok_pi _ _ ?E ?ss (restrict (w_H ?W) ?ms) |- SRr _ _ (mkCfg _ ?md) ?Q =>
    let K := eval vm_compute in (run_K A_LIM bcs_Bx SH ss) in
    let rr := eval vm_compute in (sym_run_toN_pi_tok transport_tpi transport_tw K bcs_Bx bcs_Bspan SH FUEL stop ss) in
    lazymatch rr with
    | (?st', ?res) =>
      lazymatch goal with
      | HSH : sh_ok _ _ _ E _, HEI : img_env _ _ E, HAG : env_agree 512 ?E0 E |- _ =>
        apply (bcs_run bcs_Bx bcs_Bspan SH W E ss ms md K stop st' res Q ltac:(unfold A_LIM; lia) HEI HS HSH
                 ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) I
                 ltac:(apply Forall_nil) ltac:(vm_compute; reflexivity));
        clear HS HSH HEI;
        let ws := fresh "ws" in let msn := fresh "ms" in let mat := fresh "mat" in
        let Hlen := fresh "Hlen" in let Hm := fresh "Hmem" in
        intros ws msn mat Hlen HEI HS HSH Hm;
        rewrite ?wvb_collapse;
        apply (bcs_agree_extK E0 E K ws ltac:(lia)) in HAG
      end
    end
  end.

(* The two arms of the branch the state is stuck at. *)
Ltac bcs_branch SH :=
  lazymatch goal with
  | HS : st_ok_pi _ _ ?E ?ss (restrict (w_H ?W) ?ms) |- SRr _ _ (mkCfg _ ?md) ?Q =>
    let K := eval vm_compute in (run_K A_LIM bcs_Bx SH ss) in
    let why := psym_why_tok transport_tpi transport_tw K bcs_Bx bcs_Bspan SH (start K bcs_Bx bcs_Bspan SH ss) in
    lazymatch why with
    | SR_branch ?c ?a ?b =>
      apply (paj_branch (PI := PI_transport) W E ss ms md Q c a b HS); clear HS;
      let Hc := fresh "Hc" in intros Hc HS
    end
  end.

(* The value of register r in the machine state HS describes. *)
Ltac bcs_reg HS r v H tac :=
  lazymatch type of HS with
  | st_ok_pi _ _ ?Ex ?ssx (restrict ?Hh ?msx) =>
      let e := eval vm_compute in (sr_get (ss_regs ssx) r) in
      assert (H : YK11.getr (ms_regs msx) r = v) by
        (refine (eq_trans (st_ok_pi_restrict_reg Hh Ex ssx msx r HS) _); change (sv_denot Ex e = v); tac)
  end.

(* The machine state at the stop: its shape and its memory. *)
Ltac bcs_shape :=
  lazymatch goal with HS : st_ok_pi _ _ _ _ _ |- _ => pmkst HS end;
  repeat match goal with H : ms_mem ?a = ms_mem ?b |- _ => rewrite H end;
  cbn [ms_mem YK11.mkst].

(* ------------------------------------------------------------------ *)
(* The scan                                                            *)
(* ------------------------------------------------------------------ *)

Section scan. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Local Abbreviation segs := tfibsegs.
Local Abbreviation VAL := (@pa_val _ transport_listing PI_transport).
Local Abbreviation BASE := (@pa_val _ transport_listing PI_transport A_TEXT).

Definition bcs_E (r : bvmap 5 word) (b0 b1 b3 : Z) : env :=
  Eimg (PI := PI_transport) (Ereg r [w64 b0; w64 b1; w64 b3]).

Lemma bcs_ew_reg : forall (r : bvmap 5 word) extra n (x : bv 5), (n < 32)%nat -> Z.of_nat n = bv_unsigned x ->
  ew (Eimg (PI := PI_transport) (Ereg r extra)) n = YK11.getr r x.
Proof. intros r extra n x Hn Hx. rewrite Eimg_low by (unfold A_TEXT; lia). apply ew_Ereg_nat. exact Hx. Qed.

Lemma bcs_E_ex : forall r b0 b1 b3,
  ew (bcs_E r b0 b1 b3) 32 = w64 b0 /\ ew (bcs_E r b0 b1 b3) 33 = w64 b1 /\ ew (bcs_E r b0 b1 b3) 34 = w64 b3.
Proof.
  intros r b0 b1 b3. unfold bcs_E. rewrite !Eimg_low by (unfold A_TEXT; lia).
  split; [exact (ew_Ereg_extra r _ 0) | split; [exact (ew_Ereg_extra r _ 1) | exact (ew_Ereg_extra r _ 2)]].
Qed.

Lemma bcs_agree32 : forall (r : bvmap 5 word) extra E,
  env_agree 512 (Eimg (PI := PI_transport) (Ereg r extra)) E -> env_agree 32 (Ereg r extra) E.
Proof.
  intros r extra E [H1 H2]. split.
  - intros n Hn. rewrite (H1 n ltac:(lia)). apply Eimg_low. unfold A_TEXT. lia.
  - rewrite H2. reflexivity.
Qed.

(* The registers of l the run kept, from the entry registers r0 (env Eimg (Ereg r0 ex)). *)
Ltac bcs_kr r0 ex l KR :=
  lazymatch goal with
  | HS : st_ok_pi _ _ ?Ex ?ssx (restrict (w_H ?Wx) ?msx), HAG : env_agree 512 _ ?Ex |- _ =>
    pose proof (regs_kept_of_st_ok_pi Ex ssx (restrict (w_H Wx) msx) r0 ex l HS (bcs_agree32 r0 ex Ex HAG)
      ltac:(vm_compute; reflexivity)) as KR
  end.

Lemma bcs_chunk1 : forall (E : env) (m : word -> option byte) (k : nat) (b o a v : Z),
  ew E k = w64 v -> 0 <= v < 256 -> b + o = a -> val_mem segs m a 1 v ->
  YP09.chunk_ok segs E m b (YP09.mkChunk o (CVal 1 (SOff k 0))).
Proof.
  intros E m k b o a v Hk Hv Ha Hm.
  apply (chunk_ok_val segs E m b o 1 (SOff k 0) v).
  - cbn [sv_denot]. rewrite Hk, Z.add_0_r. unfold w64. rewrite unsigned_lit_small by lia. reflexivity.
  - cbn. lia.
  - cbn. lia.
  - rewrite Ha. exact Hm.
Qed.

(* The seat of turn i at +0x20c: s3 = p, a1 = p + 1, the three bytes in the region. *)
Lemma bcs_entry : forall (W : world segs) (r : bvmap 5 word) (mem : word -> option byte) (p b0 b1 b3 : Z),
  YK11.getr r 19 = w64 p -> YK11.getr r 11 = w64 (p + 1) -> YK11.getr r 25 = w64 SHADOW_OFF ->
  4096 <= p -> p + 1 <= bcs_PTRHI ->
  0 <= b0 < 256 -> 0 <= b1 < 256 -> 0 <= b3 < 256 ->
  val_mem segs (mrestrict (w_H W) mem) p 1 b0 ->
  val_mem segs (mrestrict (w_H W) mem) (p + 1) 1 b1 ->
  val_mem segs (mrestrict (w_H W) mem) (p + 3) 1 b3 ->
  st_ok_pi segs VAL (bcs_E r b0 b1 b3) bcs_ss
    (restrict (w_H W) (@YK11.mkst fx r (Z_to_bv 64 (BASE + SC_AT 0x20c)) mem (YK11.seg_rom segs))).
Proof.
  intros W r mem p b0 b1 b3 R19 R11 R25 Hp1 Hp2 HB0 HB1 HB3 V0 V1 V3.
  unfold bcs_PTRHI in Hp2.
  destruct (bcs_E_ex r b0 b1 b3) as (E32 & E33 & E34).
  assert (U19 : bv_unsigned (ew (bcs_E r b0 b1 b3) 19) = p)
    by (unfold bcs_E; rewrite (bcs_ew_reg r _ 19 19%bv ltac:(lia) eq_refl), R19; unfold w64;
        apply unsigned_lit_small; lia).
  assert (U11 : bv_unsigned (ew (bcs_E r b0 b1 b3) 11) = p + 1)
    by (unfold bcs_E; rewrite (bcs_ew_reg r _ 11 11%bv ltac:(lia) eq_refl), R11; unfold w64;
        apply unsigned_lit_small; lia).
  assert (U25 : bv_unsigned (ew (bcs_E r b0 b1 b3) 25) = SHADOW_OFF)
    by (unfold bcs_E; rewrite (bcs_ew_reg r _ 25 25%bv ltac:(lia) eq_refl), R25; unfold w64;
        apply unsigned_lit_small; unfold SHADOW_OFF; lia).
  assert (U32 : bv_unsigned (ew (bcs_E r b0 b1 b3) 32) = b0)
    by (rewrite E32; unfold w64; apply unsigned_lit_small; lia).
  assert (U33 : bv_unsigned (ew (bcs_E r b0 b1 b3) 33) = b1)
    by (rewrite E33; unfold w64; apply unsigned_lit_small; lia).
  assert (U34 : bv_unsigned (ew (bcs_E r b0 b1 b3) 34) = b3)
    by (rewrite E34; unfold w64; apply unsigned_lit_small; lia).
  rewrite restrict_mkst_fx. unfold bcs_ss.
  apply (@pa_entry_st_ok_full fx rc transport_listing PI_transport).
  - apply regs_ok_Eimg_Ereg.
  - vm_compute. reflexivity.
  - apply Forall_cons; [|apply Forall_nil]. unfold bcs_rg, YP09.region_ok.
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val]. rewrite U11.
    split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
    apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]]].
    + apply (bcs_chunk1 _ _ 32 (p + 1) (-1) p b0); [exact E32 | lia | lia | exact V0].
    + apply (bcs_chunk1 _ _ 33 (p + 1) 0 (p + 1) b1); [exact E33 | lia | lia | exact V1].
    + apply (bcs_chunk1 _ _ 34 (p + 1) 2 (p + 3) b3); [exact E34 | lia | lia | exact V3].
  - exact (conj I I).
  - unfold facts_ok, bcs_G. cbn [f_atoms f_conds f_alias atoms_ok conds_ok alias_ok].
    unfold afact_ok, bcs_PTR, bcs_PTRHI. cbn [af_lo af_hi af_al2].
    rewrite U25, U19, U11, U32, U33, U34. rewrite !Z.pow_0_r, !Z.mod_1_r. unfold SHADOW_OFF.
    repeat split; try exact I; lia.
Qed.

(* The shadow entry of turn i: [p, p + 4) inside the addressable range [a, a + n). *)
Lemma bcs_shok : forall (W : world segs) (r : bvmap 5 word) (mem : word -> option byte) (b0 b1 b3 a n p : Z),
  YK11.getr r 19 = w64 p -> YK11.getr r 25 = w64 SHADOW_OFF -> 0 <= p < 2 ^ 64 ->
  range_addressable (aview segs (w_H W) mem) SHADOW_OFF a n -> a <= p -> p + 4 <= a + n ->
  (forall x, a <= x < a + n -> ~ (SHADOW_OFF <= x < SHADOW_OFF + 17592186044416)) ->
  sh_ok segs bcs_Bx bcs_SH (bcs_E r b0 b1 b3) (mrestrict (w_H W) mem).
Proof.
  intros W r mem b0 b1 b3 a n p R19 R25 Hp HRA Ha1 Ha2 Happ.
  apply Forall_cons; [|apply Forall_nil].
  apply (shent_ok_of_range segs (w_H W) mem (bcs_E r b0 b1 b3) bcs_Bx 19%nat a n p 0 4).
  - exact HRA.
  - unfold bcs_Bx. apply U_atom; [|unfold SHADOW_OFF; lia].
    unfold bcs_E. rewrite (bcs_ew_reg r _ 25 25%bv ltac:(lia) eq_refl). exact R25.
  - apply U_atom; [|lia]. unfold bcs_E. rewrite (bcs_ew_reg r _ 19 19%bv ltac:(lia) eq_refl). exact R19.
  - lia.
  - lia.
  - intros x Hx. cbn [Z.min Z.max] in Hx. apply Happ. lia.
Qed.

(* The facts of the walk the scan uses: the body's bytes, their shadow (trans_src_ok at the cut's state), the slot of
   len, the release. The body's place is known when there are bytes (the scan reads them only when len >= 4). *)
Variables (W2 : world segs) (mem2 : word -> option byte) (regs : bvmap 5 word) (body : Z) (bb : list byte)
  (sp1 F : Z).
Variable Q : world segs -> config -> Prop.
Variable J : Model -> Prop.
Hypothesis HJmat : forall md X, J md -> J (with_vm_backing (m_vm_lazy md) X md).
Hypothesis HREL : forall (regs' : bvmap 5 word) (md' : Model),
  bc_regs_rel regs regs' sp1 F -> YK11.getr regs' 10 = w64 (body_check bb) -> J md' ->
  SRr segs W2 (mkCfg (@YK11.mkst fx regs' (Z_to_bv 64 (BASE + BC_REL)) mem2 (YK11.seg_rom segs)) md') Q.
Hypothesis Hb4096 : (0 < length bb)%nat -> 4096 <= body.
Hypothesis Hbhi : (0 < length bb)%nat -> body + Z.of_nat (length bb) <= 140737488355327.
Hypothesis HRA : range_addressable (aview segs (w_H W2) mem2) SHADOW_OFF body (Z.of_nat (length bb)).
Hypothesis HAPP : forall x, body <= x < body + Z.of_nat (length bb) ->
  ~ (SHADOW_OFF <= x < SHADOW_OFF + 17592186044416).
Hypothesis HG : garr8 segs (mrestrict (w_H W2) mem2) body (map bz bb).
Hypothesis Hslot : rdword (aview segs (w_H W2) mem2) (sp1 + 16) = Some (Z.of_nat (length bb)).
Hypothesis Hsp1 : 0 <= sp1 <= 2 ^ 47.

Local Abbreviation bcs_at pc r md :=
  (mkCfg (@YK11.mkst fx r (Z_to_bv 64 (BASE + pc)) mem2 (YK11.seg_rom segs)) md).

Lemma bcs_byte : forall j, (j < length bb)%nat ->
  val_mem segs (mrestrict (w_H W2) mem2) (body + Z.of_nat j) 1 (at8 bb j) /\ 0 <= at8 bb j < 256.
Proof.
  intros j Hj. assert (Hj' : (j < length (map bz bb))%nat) by (rewrite length_map; exact Hj).
  destruct (HG j Hj') as [Hv Hr]. rewrite bcs_nth_bz in Hv, Hr. exact (conj Hv Hr).
Qed.

(* The registers at +0x20c before turn i. *)
Definition bcs_inv (r : bvmap 5 word) (i : nat) : Prop :=
  YK11.getr r 19 = w64 (body + Z.of_nat i) /\ YK11.getr r 11 = w64 (body + Z.of_nat i + 1) /\
  YK11.getr r 20 = w64 (Z.of_nat (length bb) - 3 - Z.of_nat i) /\
  YK11.getr r 12 = w64 240 /\ YK11.getr r 13 = w64 19 /\ YK11.getr r 14 = w64 112 /\
  YK11.getr r 25 = w64 SHADOW_OFF /\ bc_regs_rel regs r sp1 F.

(* What the next turn gives. *)
Definition bcs_K (i : nat) : Prop :=
  forall (r : bvmap 5 word) (md : Model), (S i + 3 < length bb)%nat ->
    (forall j, (j < S i)%nat -> sys_hit bb j = false) -> bcs_inv r (S i) -> J md ->
    SRr segs W2 (bcs_at (SC_AT 0x20c) r md) Q.

Lemma bcs_inv_kept : forall r1 r2 i, bcs_inv r1 i ->
  (forall x, In x kp_rel -> YK11.getr r2 x = YK11.getr r1 x) ->
  (forall x, In x kp_lp -> YK11.getr r2 x = YK11.getr r1 x) -> bcs_inv r2 i.
Proof.
  intros r1 r2 i (R19 & R11 & R20 & R12 & R13 & R14 & R25 & HRL) K1 K2. unfold bcs_inv.
  split; [rewrite K2; [exact R19 | bcs_kin]|].
  split; [rewrite K2; [exact R11 | bcs_kin]|].
  split; [rewrite K2; [exact R20 | bcs_kin]|].
  split; [rewrite K2; [exact R12 | bcs_kin]|].
  split; [rewrite K2; [exact R13 | bcs_kin]|].
  split; [rewrite K2; [exact R14 | bcs_kin]|].
  split; [rewrite K2; [exact R25 | bcs_kin]|].
  exact (bcs_rel_kept regs r1 r2 sp1 F HRL K1).
Qed.

(* +0x25c .. +0x268: s3, a1 one up, s4 one down; `bnez s4` back to +0x20c, else +0x294 and the release. *)
Lemma bcs_bump : forall (i : nat) (r0 : bvmap 5 word) (md : Model),
  (i + 3 < length bb)%nat -> (forall j, (j <= i)%nat -> sys_hit bb j = false) -> bcs_inv r0 i -> J md -> bcs_K i ->
  SRr segs W2 (bcs_at (SC_AT 0x25c) r0 md) Q.
Proof.
  intros i r0 md Hi Hpre Hinv HJ HK. unfold bcs_K in HK.
  pose proof (Hb4096 ltac:(lia)) as Hb1. pose proof (Hbhi ltac:(lia)) as Hb2.
  pose proof Hinv as (R19 & R11 & R20 & R12 & R13 & R14 & R25 & HRL).
  assert (HS : st_ok_pi segs VAL (Eimg (PI := PI_transport) (Ereg r0 [])) bcb_ss
    (restrict (w_H W2) (@YK11.mkst fx r0 (Z_to_bv 64 (BASE + SC_AT 0x25c)) mem2 (YK11.seg_rom segs)))).
  { rewrite restrict_mkst_fx. unfold bcb_ss. apply (@pa_entry_st_ok_full fx rc transport_listing PI_transport).
    - apply regs_ok_Eimg_Ereg.
    - vm_compute. reflexivity.
    - apply Forall_nil.
    - exact I.
    - exact (conj I (conj I I)). }
  assert (HSH : sh_ok segs bcs_Bx [] (Eimg (PI := PI_transport) (Ereg r0 [])) (mrestrict (w_H W2) mem2))
    by apply Forall_nil.
  assert (HEI : img_env VAL A_LIM (Eimg (PI := PI_transport) (Ereg r0 []))) by apply Eimg_env.
  pose proof (env_agree_refl 512 (Eimg (PI := PI_transport) (Ereg r0 []))) as HAG.
  assert (X19 : ew (Eimg (PI := PI_transport) (Ereg r0 [])) 19 = w64 (body + Z.of_nat i))
    by (rewrite (bcs_ew_reg r0 _ 19 19%bv ltac:(lia) eq_refl); exact R19).
  assert (X11 : ew (Eimg (PI := PI_transport) (Ereg r0 [])) 11 = w64 (body + Z.of_nat i + 1))
    by (rewrite (bcs_ew_reg r0 _ 11 11%bv ltac:(lia) eq_refl); exact R11).
  assert (X20 : ew (Eimg (PI := PI_transport) (Ereg r0 [])) 20 = w64 (Z.of_nat (length bb) - 3 - Z.of_nat i))
    by (rewrite (bcs_ew_reg r0 _ 20 20%bv ltac:(lia) eq_refl); exact R20).
  bcs_step ([] : list shent) (SC_AT 0x20c).
  bcs_branch ([] : list shent).
  - (* s4 - 1 <> 0: turn i + 1 *)
    rewrite branch_ne_U in Hc.
    rewrite (bcs_Uoff _ _ 20 _ (-1) HAG ltac:(lia) X20 ltac:(lia) ltac:(lia)), U_lit in Hc by lia.
    apply negb_true_iff, Z.eqb_neq in Hc.
    bcs_step ([] : list shent) (SC_AT 0x20c).
    bcs_kr r0 ([] : list word) kp_rel KR1. bcs_kr r0 ([] : list word) kp_bp KR2.
    bcs_reg HS (19%bv : bv 5) (w64 (body + Z.of_nat (S i))) Q19
      ltac:(rewrite (bcs_den _ _ 19 _ 1 HAG ltac:(lia) X19 ltac:(lia)); f_equal; lia).
    bcs_reg HS (11%bv : bv 5) (w64 (body + Z.of_nat (S i) + 1)) Q11
      ltac:(rewrite (bcs_den _ _ 11 _ 1 HAG ltac:(lia) X11 ltac:(lia)); f_equal; lia).
    bcs_reg HS (20%bv : bv 5) (w64 (Z.of_nat (length bb) - 3 - Z.of_nat (S i))) Q20
      ltac:(rewrite (bcs_den _ _ 20 _ (-1) HAG ltac:(lia) X20 ltac:(lia)); f_equal; lia).
    bcs_shape.
    apply HK; [lia | intros j Hj; apply Hpre; lia | | apply HJmat; exact HJ].
    unfold bcs_inv. split; [exact Q19|]. split; [exact Q11|]. split; [exact Q20|].
    split; [etransitivity; [apply KR2; bcs_kin | exact R12]|].
    split; [etransitivity; [apply KR2; bcs_kin | exact R13]|].
    split; [etransitivity; [apply KR2; bcs_kin | exact R14]|].
    split; [etransitivity; [apply KR2; bcs_kin | exact R25]|].
    exact (bcs_rel_kept regs r0 _ sp1 F HRL KR1).
  - (* s4 - 1 = 0: the scan ends, a0 = 0 *)
    rewrite branch_ne_U in Hc.
    rewrite (bcs_Uoff _ _ 20 _ (-1) HAG ltac:(lia) X20 ltac:(lia) ltac:(lia)), U_lit in Hc by lia.
    apply negb_false_iff, Z.eqb_eq in Hc.
    assert (Hbc : body_check bb = 0)
      by (apply bcs_bc0, system_at_false; intros j Hj; apply Hpre; lia).
    bcs_step ([] : list shent) (SC_AT 0x298).
    bcs_kr r0 ([] : list word) kp_rel KR1.
    bcs_reg HS (10%bv : bv 5) (w64 (body_check bb)) Q10 ltac:(rewrite Hbc; reflexivity).
    bcs_shape.
    apply HREL; [exact (bcs_rel_kept regs r0 _ sp1 F HRL KR1) | exact Q10 | apply HJmat; exact HJ].
Qed.

(* +0x20c .. +0x258, turn i: the three checked loads and compares. *)
Lemma bcs_body : forall (i : nat) (r0 : bvmap 5 word) (md : Model),
  (i + 3 < length bb)%nat -> (forall j, (j < i)%nat -> sys_hit bb j = false) -> bcs_inv r0 i -> J md -> bcs_K i ->
  SRr segs W2 (bcs_at (SC_AT 0x20c) r0 md) Q.
Proof.
  intros i r0 md Hi Hpre Hinv HJ HK.
  pose proof (Hb4096 ltac:(lia)) as Hb1. pose proof (Hbhi ltac:(lia)) as Hb2.
  destruct (bcs_byte i ltac:(lia)) as [V0 B0].
  destruct (bcs_byte (S i) ltac:(lia)) as [V1 B1].
  destruct (bcs_byte (S (S (S i))) ltac:(lia)) as [V3 B3].
  replace (body + Z.of_nat (S i)) with (body + Z.of_nat i + 1) in V1 by lia.
  replace (body + Z.of_nat (S (S (S i)))) with (body + Z.of_nat i + 3) in V3 by lia.
  remember (at8 bb i) as b0 eqn:Eb0. remember (at8 bb (S i)) as b1 eqn:Eb1.
  remember (at8 bb (S (S (S i)))) as b3 eqn:Eb3.
  pose proof Hinv as (R19 & R11 & R20 & R12 & R13 & R14 & R25 & HRL).
  pose proof (bcs_entry W2 r0 mem2 (body + Z.of_nat i) b0 b1 b3 R19 R11 R25 ltac:(lia)
    ltac:(unfold bcs_PTRHI; lia) B0 B1 B3 V0 V1 V3) as HS.
  pose proof (bcs_shok W2 r0 mem2 b0 b1 b3 body (Z.of_nat (length bb)) (body + Z.of_nat i) R19 R25 ltac:(lia)
    HRA ltac:(lia) ltac:(lia) HAPP) as HSH.
  assert (HEI : img_env VAL A_LIM (bcs_E r0 b0 b1 b3)) by apply Eimg_env.
  pose proof (env_agree_refl 512 (bcs_E r0 b0 b1 b3)) as HAG.
  destruct (bcs_E_ex r0 b0 b1 b3) as (X32 & X33 & X34).
  assert (X12 : ew (bcs_E r0 b0 b1 b3) 12 = w64 240)
    by (unfold bcs_E; rewrite (bcs_ew_reg r0 _ 12 12%bv ltac:(lia) eq_refl); exact R12).
  assert (X13 : ew (bcs_E r0 b0 b1 b3) 13 = w64 19)
    by (unfold bcs_E; rewrite (bcs_ew_reg r0 _ 13 13%bv ltac:(lia) eq_refl); exact R13).
  assert (X14 : ew (bcs_E r0 b0 b1 b3) 14 = w64 112)
    by (unfold bcs_E; rewrite (bcs_ew_reg r0 _ 14 14%bv ltac:(lia) eq_refl); exact R14).
  bcs_step bcs_SH (SC_AT 0x25c).
  bcs_branch bcs_SH.
  - (* body[i] <> 0xf0 *)
    rewrite branch_ne_U in Hc.
    rewrite (bcs_U _ _ 32 b0 HAG ltac:(lia) X32 ltac:(lia)), (bcs_U _ _ 12 240 HAG ltac:(lia) X12 ltac:(lia)) in Hc.
    apply negb_true_iff, Z.eqb_neq in Hc.
    bcs_step bcs_SH (SC_AT 0x25c).
    bcs_kr r0 [w64 b0; w64 b1; w64 b3] kp_rel KR1. bcs_kr r0 [w64 b0; w64 b1; w64 b3] kp_lp KR2.
    bcs_shape.
    apply (bcs_bump i _ _ Hi).
    + intros j Hj. destruct (Nat.eq_dec j i) as [->|Hne];
        [apply bcs_hit0; rewrite <- Eb0; exact Hc | apply Hpre; lia].
    + apply (bcs_inv_kept r0 _ i Hinv); [exact KR1 | exact KR2].
    + apply HJmat. exact HJ.
    + exact HK.
  - (* body[i] = 0xf0 *)
    rewrite branch_ne_U in Hc.
    rewrite (bcs_U _ _ 32 b0 HAG ltac:(lia) X32 ltac:(lia)), (bcs_U _ _ 12 240 HAG ltac:(lia) X12 ltac:(lia)) in Hc.
    apply negb_false_iff, Z.eqb_eq in Hc.
    bcs_step bcs_SH (SC_AT 0x25c).
    bcs_branch bcs_SH.
    + (* body[i + 1] <> 0x13 *)
      rewrite branch_ne_U in Hc0.
      rewrite (bcs_U _ _ 33 b1 HAG ltac:(lia) X33 ltac:(lia)), (bcs_U _ _ 13 19 HAG ltac:(lia) X13 ltac:(lia))
        in Hc0.
      apply negb_true_iff, Z.eqb_neq in Hc0.
      bcs_step bcs_SH (SC_AT 0x25c).
      bcs_kr r0 [w64 b0; w64 b1; w64 b3] kp_rel KR1. bcs_kr r0 [w64 b0; w64 b1; w64 b3] kp_lp KR2.
      bcs_shape.
      apply (bcs_bump i _ _ Hi).
      * intros j Hj. destruct (Nat.eq_dec j i) as [->|Hne];
          [apply bcs_hit1; rewrite <- Eb1; exact Hc0 | apply Hpre; lia].
      * apply (bcs_inv_kept r0 _ i Hinv); [exact KR1 | exact KR2].
      * apply HJmat. exact HJ.
      * exact HK.
    + (* body[i + 1] = 0x13 *)
      rewrite branch_ne_U in Hc0.
      rewrite (bcs_U _ _ 33 b1 HAG ltac:(lia) X33 ltac:(lia)), (bcs_U _ _ 13 19 HAG ltac:(lia) X13 ltac:(lia))
        in Hc0.
      apply negb_false_iff, Z.eqb_eq in Hc0.
      bcs_step bcs_SH (SC_AT 0x25c).
      bcs_branch bcs_SH.
      * (* body[i + 3] = 0x70: F0 13 xx 70 at i, a0 = -10 *)
        rewrite branch_eq_U in Hc1.
        rewrite (bcs_U _ _ 34 b3 HAG ltac:(lia) X34 ltac:(lia)), (bcs_U _ _ 14 112 HAG ltac:(lia) X14 ltac:(lia))
          in Hc1.
        apply Z.eqb_eq in Hc1.
        assert (Hhit : sys_hit bb i = true) by (apply bcs_hit_true; congruence).
        assert (Hbc : body_check bb = -10)
          by (apply (proj2 (body_check_refused bb)), (proj2 (system_at_true bb)); exists i; split; [lia | exact Hhit]).
        bcs_step bcs_SH (SC_AT 0x298).
        bcs_kr r0 [w64 b0; w64 b1; w64 b3] kp_rel KR1.
        bcs_reg HS (10%bv : bv 5) (w64 (body_check bb)) Q10
          ltac:(cbn [sv_denot]; rewrite Hbc; unfold w64; apply bv_eq; rewrite !Z_to_bv_unsigned; reflexivity).
        bcs_shape.
        apply HREL; [exact (bcs_rel_kept regs r0 _ sp1 F HRL KR1) | exact Q10 | apply HJmat; exact HJ].
      * (* body[i + 3] <> 0x70 *)
        rewrite branch_eq_U in Hc1.
        rewrite (bcs_U _ _ 34 b3 HAG ltac:(lia) X34 ltac:(lia)), (bcs_U _ _ 14 112 HAG ltac:(lia) X14 ltac:(lia))
          in Hc1.
        apply Z.eqb_neq in Hc1.
        bcs_step bcs_SH (SC_AT 0x25c).
        bcs_kr r0 [w64 b0; w64 b1; w64 b3] kp_rel KR1. bcs_kr r0 [w64 b0; w64 b1; w64 b3] kp_lp KR2.
        bcs_shape.
        apply (bcs_bump i _ _ Hi).
        -- intros j Hj. destruct (Nat.eq_dec j i) as [->|Hne];
             [apply bcs_hit3; rewrite <- Eb3; exact Hc1 | apply Hpre; lia].
        -- apply (bcs_inv_kept r0 _ i Hinv); [exact KR1 | exact KR2].
        -- apply HJmat. exact HJ.
        -- exact HK.
Qed.

(* The loop, by induction on the turns left. *)
Lemma bcs_loop : forall (n i : nat) (r0 : bvmap 5 word) (md : Model),
  n = (length bb - 3 - i)%nat -> (i + 3 < length bb)%nat -> (forall j, (j < i)%nat -> sys_hit bb j = false) ->
  bcs_inv r0 i -> J md -> SRr segs W2 (bcs_at (SC_AT 0x20c) r0 md) Q.
Proof.
  induction n as [|n IH]; intros i r0 md Hn Hi Hpre Hinv HJ; [lia|].
  apply (bcs_body i r0 md Hi Hpre Hinv HJ). unfold bcs_K.
  intros r1 md1 Hi1 Hpre1 Hinv1 HJ1. exact (IH (S i) r1 md1 ltac:(lia) Hi1 Hpre1 Hinv1 HJ1).
Qed.

(* +0x1ec: len from the slot; len < 4 gives a0 = 0 and the release, else the loop from turn 0. *)
Lemma bcs_head : forall (r2 : bvmap 5 word) (md : Model),
  bc_regs_scan regs r2 body sp1 F -> J md -> SRr segs W2 (bcs_at BC_SCAN r2 md) Q.
Proof using HJmat HREL Hb4096 Hbhi HRA HAPP HG Hslot Hsp1.
  intros r2 md (HRL & R19 & R25) HJ.
  pose proof HRL as (R2 & R3 & R4 & R8 & R9 & R23 & R24).
  assert (U9 : bv_unsigned (ew (Eimg (PI := PI_transport) (Ereg r2 [w64 (Z.of_nat (length bb))])) 9) = sp1)
    by (rewrite (bcs_ew_reg r2 _ 9 9%bv ltac:(lia) eq_refl), R9; unfold w64; apply unsigned_lit_small; lia).
  assert (X32 : ew (Eimg (PI := PI_transport) (Ereg r2 [w64 (Z.of_nat (length bb))])) 32
                = w64 (Z.of_nat (length bb)))
    by (rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra r2 _ 0)).
  assert (X19 : ew (Eimg (PI := PI_transport) (Ereg r2 [w64 (Z.of_nat (length bb))])) 19 = w64 body)
    by (rewrite (bcs_ew_reg r2 _ 19 19%bv ltac:(lia) eq_refl); exact R19).
  assert (HS : st_ok_pi segs VAL (Eimg (PI := PI_transport) (Ereg r2 [w64 (Z.of_nat (length bb))])) bch_ss
    (restrict (w_H W2) (@YK11.mkst fx r2 (Z_to_bv 64 (BASE + BC_SCAN)) mem2 (YK11.seg_rom segs)))).
  { rewrite restrict_mkst_fx. unfold bch_ss.
    apply (@pa_entry_st_ok_full fx rc transport_listing PI_transport).
    - apply regs_ok_Eimg_Ereg.
    - vm_compute. reflexivity.
    - apply Forall_cons; [|apply Forall_nil]. unfold bch_rg, YP09.region_ok.
      cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val]. rewrite U9.
      split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
      apply Forall_cons; [|apply Forall_nil].
      apply (chunk_ok_val segs _ _ sp1 16 8 (SOff 32 0) (Z.of_nat (length bb))).
      + cbn [sv_denot]. rewrite X32, Z.add_0_r. unfold w64. rewrite unsigned_lit_small by lia. reflexivity.
      + cbn. lia.
      + cbn. lia.
      + apply val_mem_of_rdword. exact Hslot.
    - exact (conj I I).
    - exact (conj I (conj I I)). }
  assert (HSH : sh_ok segs bcs_Bx [] (Eimg (PI := PI_transport) (Ereg r2 [w64 (Z.of_nat (length bb))]))
                  (mrestrict (w_H W2) mem2)) by apply Forall_nil.
  assert (HEI : img_env VAL A_LIM (Eimg (PI := PI_transport) (Ereg r2 [w64 (Z.of_nat (length bb))])))
    by apply Eimg_env.
  pose proof (env_agree_refl 512 (Eimg (PI := PI_transport) (Ereg r2 [w64 (Z.of_nat (length bb))]))) as HAG.
  bcs_step ([] : list shent) (SC_AT 0x20c).
  bcs_branch ([] : list shent).
  - (* len < 4: a0 = 0 *)
    rewrite branch_ltu_U in Hc.
    rewrite (bcs_U _ _ 32 _ HAG ltac:(lia) X32 ltac:(lia)), U_lit in Hc by lia.
    apply Z.ltb_lt in Hc.
    assert (Hbc : body_check bb = 0) by (apply bcs_bc0, system_at_false; intros j Hj; lia).
    bcs_step ([] : list shent) (SC_AT 0x298).
    bcs_kr r2 [w64 (Z.of_nat (length bb))] kp_rel KR1.
    bcs_reg HS (10%bv : bv 5) (w64 (body_check bb)) Q10 ltac:(rewrite Hbc; reflexivity).
    bcs_shape.
    apply HREL; [exact (bcs_rel_kept regs r2 _ sp1 F HRL KR1) | exact Q10 | apply HJmat; exact HJ].
  - (* len >= 4: the loop from turn 0 *)
    rewrite branch_ltu_U in Hc.
    rewrite (bcs_U _ _ 32 _ HAG ltac:(lia) X32 ltac:(lia)), U_lit in Hc by lia.
    apply Z.ltb_ge in Hc.
    pose proof (Hb4096 ltac:(lia)) as Hb1. pose proof (Hbhi ltac:(lia)) as Hb2.
    bcs_step ([] : list shent) (SC_AT 0x20c).
    bcs_kr r2 [w64 (Z.of_nat (length bb))] kp_rel KR1. bcs_kr r2 [w64 (Z.of_nat (length bb))] kp_hd KR2.
    bcs_reg HS (11%bv : bv 5) (w64 (body + Z.of_nat 0 + 1)) Q11
      ltac:(rewrite (bcs_den _ _ 19 _ 1 HAG ltac:(lia) X19 ltac:(lia)); f_equal; lia).
    bcs_reg HS (20%bv : bv 5) (w64 (Z.of_nat (length bb) - 3 - Z.of_nat 0)) Q20
      ltac:(rewrite (bcs_den _ _ 32 _ (-3) HAG ltac:(lia) X32 ltac:(lia)); f_equal; lia).
    bcs_reg HS (12%bv : bv 5) (w64 240) Q12 ltac:(reflexivity).
    bcs_reg HS (13%bv : bv 5) (w64 19) Q13 ltac:(reflexivity).
    bcs_reg HS (14%bv : bv 5) (w64 112) Q14 ltac:(reflexivity).
    bcs_shape.
    apply (bcs_loop (length bb - 3 - 0) 0 _ _ eq_refl); [lia | intros j Hj; lia | | apply HJmat; exact HJ].
    unfold bcs_inv.
    split; [etransitivity; [apply KR2; bcs_kin | rewrite R19; f_equal; lia]|].
    split; [exact Q11|]. split; [exact Q20|]. split; [exact Q12|]. split; [exact Q13|]. split; [exact Q14|].
    split; [etransitivity; [apply KR2; bcs_kin | exact R25]|].
    exact (bcs_rel_kept regs r2 _ sp1 F HRL KR1).
Qed.

End scan.

(* ------------------------------------------------------------------ *)
(* The cut                                                             *)
(* ------------------------------------------------------------------ *)

Section x. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable B : asyms.
Variable MT : ameter_ops.

Lemma bc_scan : @bc_rel_stmt fx rc B MT -> @bc_scan_stmt fx rc B MT.
Proof.
  intros HRELS. unfold bc_scan_stmt.
  intros HLAWS STK sp0 FP lyx Sx W0 mem0 md0 own lyc Sc W memc mdc k regs body bb pos sp1 F W2 regs2 mem2 md2
    ly2 S2 HFIX HCUR HRS.
  pose proof HLAWS as (_ & LAWS & _).
  pose proof HFIX as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Esp1 & _).
  pose proof HCUR as (HJ & Hperm & _ & _ & Hslot & _ & _ & HG & HSRC).
  pose proof HJ as (HAR & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hstk & _).
  destruct Hstk as (_ & _ & Hlo & Hlosp & Hsphi & Hhi47 & _).
  pose proof asan_consts as (C1 & _).
  (* the body, when there are bytes: decode_rd_ok and its place at the cut's state *)
  assert (HRD : (0 < length bb)%nat -> decode_rd_ok W2 mem2 body (Z.of_nat (length bb)))
    by (intros HL; exact (trans_src_ok_rd B LAWS ly2 S2 W2 mem2 md2 body _ HAR (HSRC HL) ltac:(lia))).
  assert (HPL : (0 < length bb)%nat -> 4096 <= body /\ body + Z.of_nat (length bb) <= 140737488355327).
  { intros HL. destruct (HRD HL) as (_ & _ & _ & Ham & H0 & _).
    pose proof (trans_src_ok_place B LAWS ly2 S2 W2 mem2 md2 body _ HAR (HSRC HL) ltac:(lia)) as Hp.
    unfold amem_range, kLowMemEnd, kHighMemBeg, kHighMemEnd in Ham. destruct Hp as [Hp|Hp]; lia. }
  assert (HRA : range_addressable (aview tfibsegs (w_H W2) mem2) SHADOW_OFF body (Z.of_nat (length bb))).
  { destruct (Nat.eq_dec (length bb) 0) as [E0|E0]; [intros x Hx; lia|].
    exact (proj1 (proj2 (HRD ltac:(lia)))). }
  assert (HAPP : forall x, body <= x < body + Z.of_nat (length bb) ->
                   ~ (SHADOW_OFF <= x < SHADOW_OFF + 17592186044416)).
  { intros x Hx. destruct (HRD ltac:(lia)) as (_ & _ & _ & Ham & _).
    unfold amem_range, kLowMemEnd, kHighMemBeg, kHighMemEnd in Ham. unfold SHADOW_OFF. lia. }
  assert (HST : TRANS_BC_STK = 4400) by reflexivity.
  assert (HFF : TRANS_BC_FRAME = 160) by reflexivity.
  assert (Hsp1 : 0 <= sp1 <= 2 ^ 47).
  { rewrite HST in Hlosp. rewrite HFF in Esp1. subst sp1.
    pose proof (Z.div_pos (spZ regs - 160) 32 ltac:(lia) ltac:(lia)).
    pose proof (Z.mul_div_le (spZ regs - 160) 32 ltac:(lia)). lia. }
  lazymatch type of HCUR with ?Jf md2 =>
  lazymatch goal with |- SRr _ _ _ ?Qg =>
    refine (bcs_head W2 mem2 regs body bb sp1 F Qg Jf _ _ (fun HL => proj1 (HPL HL)) (fun HL => proj2 (HPL HL))
              HRA HAPP HG Hslot Hsp1
              regs2 md2 HRS HCUR)
  end end.
  - intros md X HJx. destruct HJx as (HJ' & Hrest).
    split; [|exact Hrest].
    apply ajournal_materialize; first [assumption | exact transport_segs_low | exact (@pa_segs_low _ transport_listing PI_transport)].
  - intros regs' md' HR H10 HJ'.
    exact (HRELS HLAWS STK sp0 FP lyx Sx W0 mem0 md0 own lyc Sc W memc mdc k regs body bb pos sp1 F W2 regs' mem2 md'
             ly2 S2 HFIX HJ' HR H10).
Qed.

End x.
