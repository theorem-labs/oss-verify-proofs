(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: restates text of projects/cgif/cgif_file_fuzzer/proofs/lib/YCbq.v:528-543, 616-634;
   projects/cgif/cgif_rgb_fuzzer/proofs/lib/YC05.v:41-45, 208-214, 230-234, for libreac/fuzz_identity's asan-ubsan build
   (lib/B). The same text also appears in projects/cgif/cgif_file_fuzzer/proofs/lib/YCbo.v:420-423, 430-444, 447-448,
   453-455, 470-475, 477-486, 489-491, 502-505, 511-514, 1255-1258. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_identity/lib/B/Prog/reac_box_name_seg_rel.v, with its module paths, module names and numbers changed; 373 of its 421 lines of code are new or changed and 1876 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libdiginet/fuzz_transport/lib/B/Prog/SendctlBRel.v, with its module paths and module names changed; 453 of its 500 lines of code are new or changed and 374 lines of the source are left out. *)
(* LLVMFuzzerTestOneInput_seg_head: proves no function (kind: segment lemma of LLVMFuzzerTestOneInput's walk).
   lc_head_ok : lc_rom_view_stmt -> lc_head_stmt (lib/A/Prog/LLVMFuzzerTestOneInput_segs.v), the segment HEAD of the
   image-A walk of fuzz_transport.asan's LLVMFuzzerTestOneInput, +0x408 .. +0x45c of the listing
   lib/A/Prog/DgnTransportList.v, from the loop head (lc_st_head) to the first instruction of arm o (lc_st_arm),
   o = the op byte mod 9. It writes no memory and calls nothing:
     +0x408 .. +0x414  the shadow byte of s9 (the cursor) and `bnez a0` to the slow path +0x132c .. +0x1334
                       (`andi`, `blt` back to +0x418, else the report call at 0x82c94);
     +0x418 .. +0x43c  the op byte (`lbu a0, 0(s9)`), s7 = s11 - 1, a0 = byte - 9 * ((byte * 57) >> 9) (the low
                       byte), s8 = s9 + 1;
     +0x440            `bltu s6, a0` (s6 = 7) to arm 8 at +0x6e8;
     +0x444 .. +0x45c  the table entry at TRANS_JT_LLVMF + 4 * a0 (`lw`, the table's address from the listing's
                       object 11) plus the table's address, `jr a0` to arm a0.
   How it is proved. The PA engine with its token shadow checks (lib/A/Prog/PaShadow.v) runs from a symbolic state
   whose only region is the op byte (atom 32, read-only): the shadow entry of the byte (range_addressable of the input
   block, YCbq.v range_addressable_of_block) decides the check, so the slow path and the report are not reached. s6 is
   pinned to the literal 7 and, after the case split on the byte mod 9 (lh_mod9: a0 is the byte mod 9 for each of the
   256 bytes), a0 to the literal op code, so the engine decides `bltu`. For ops 0 .. 7 the byte's region is dropped
   and the table's added (its 32 bytes read as the image by K1, lc_rom_view_stmt, and decided against the loaded
   segments, lh_jt_rom); the run stops at `jr a0`, the target is pinned as the code pointer of the arm and a last run
   takes the jump. Every run writes no memory, so lc_core is kept with the model's materialized part replaced
   (W_journalG.v ajournal_gx_materialize, at any FP), and the registers the cut reads are the entry's (lh_kp). *)
(* lc_head_ok takes K1 (lc_rom_view_stmt, the kit row of the read-only bytes) as its input, as the composition gives
   each segment the kit lemmas it uses. *)
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
DgnTransportSyms DgnTransportList DgnTransportAddr DgnTransportPa DgnTransportImg DgnTransportPaLib.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A Require Import AB1v AE2k ACfn.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A Require AsanCells TransportG.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A Require Import W_journalG.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import PaBase DgnTransportCg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import TransportGCg TWorldG TWorldA TImgA.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import LLVMFuzzerTestOneInput_cg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import LLVMFuzzerTestOneInput_segs.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import LLVMFuzzerTestOneInput_st.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Spec Require DgnSpec.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel Require TOps.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.
Module YK11 := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YK11.
Module TOP := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TOps.
Module DSpec := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Spec.DgnSpec.
#[global] Remove Hints OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5b.src0_sink_head
  OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5c.src0_sink
  OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5c.src0_sink_laws : typeclass_instances.

(* ------------------------------------------------------------------ *)
(* The symbolic state at the head                                       *)
(* ------------------------------------------------------------------ *)

(* s10 holds the shadow base; the shadow span the token engine checks against. *)
Definition lh_Bx : sv := SOff 26 0.
Definition lh_Bspan : Z * Z := (SHADOW_OFF, SHADOW_OFF + 2 ^ 44 - 1).
(* The shadow entry of the op byte's check: the byte at s9. *)
Definition lh_SH : list shent := [mkSHE 25 0 1].
Definition lh_PTRHI : Z := 140737488355324.
Definition lh_G : facts := mkFacts [(26%nat, mkAF SHADOW_OFF SHADOW_OFF 0); (25%nat, mkAF 4096 lh_PTRHI 0);
  (32%nat, mkAF 0 255 0)] [] [].
(* The op byte at s9, as atom 32. *)
Definition lh_rg : YP09.region := YP09.mkRegion (Some 25%nat) 0 1 0 0 [YP09.mkChunk 0 (CVal 1 (SOff 32 0))].
Definition lh_ss : sstate := mkSS LO_HEAD sr_atoms [lh_rg] None lh_G.
(* The op switch's table at TRANS_JT_LLVMF (the listing's object 11, atom A_OBJ 11): entry i, read by `lw` at
   +0x454, is arm i's distance from the table (st.v lc_rom_tab). *)
Definition lh_jtw (i : nat) : Z := transport_text + nth i LO_ARMS 0 - TRANS_JT_LLVMF.
Definition lh_rg_jt : YP09.region := YP09.mkRegion (Some (A_OBJ 11)) 0 32 0 0
  (map (fun i => YP09.mkChunk (4 * Z.of_nat i) (CVal 4 (SLit (lh_jtw i)))) (seq 0 8)).

(* ------------------------------------------------------------------ *)
(* One run of the engine over read-only regions                        *)
(* ------------------------------------------------------------------ *)

Section run. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Local Abbreviation segs := tfibsegs.
Local Abbreviation VAL := (@pa_val _ transport_listing PI_transport).

(* The run writes no memory (its regions are read-only), so the memory after it is the memory before; the model
   after it is the model before with its materialized part replaced. *)
Lemma lh_run : forall (Bx : sv) (Bspan : Z * Z) (SH : list shent) (W : world segs) (E : env) (ss : sstate)
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

(* ------------------------------------------------------------------ *)
(* Changing a symbolic state between runs (notice_seg_base.v nt_pin / nt_drop / nt_add) *)
(* ------------------------------------------------------------------ *)

Section sst. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Local Abbreviation segs := tfibsegs.
Local Abbreviation VAL := (@pa_val _ transport_listing PI_transport).
Local Abbreviation BASE := (@pa_val _ transport_listing PI_transport A_TEXT).

(* A register set to a value equal to the one it has. *)
Lemma lh_pin : forall E ss ms (r : bv 5) v,
  st_ok_pi segs VAL E ss ms -> YK11.getr (ms_regs ms) r = sv_denot E v -> bv_eqb r 0 = false ->
  st_ok_pi segs VAL E (mkSS (ss_pc ss) (sr_set (ss_regs ss) r v) (ss_mem ss) (ss_resv ss) (ss_facts ss)) ms.
Proof.
  intros E ss ms r v HS Hr Hr0. unfold st_ok_pi, abs_ss, setpc in *.
  cbn [ss_pc ss_regs ss_fregs ss_mem ss_resv ss_facts] in *.
  apply (st_ok_regs segs E (mkSST (BASE + ss_pc ss) (ss_regs ss) (ss_fregs ss) (ss_mem ss) (ss_resv ss) (ss_facts ss)) ms
    (sr_set (ss_regs ss) r v) HS).
  intros rr. cbn [ss_regs]. destruct (decide (rr = r)) as [->|Hne].
  - rewrite sr_get_set_same by exact Hr0. pose proof (st_ok_reg segs E _ ms r HS) as Hq. cbn [ss_regs] in Hq.
    rewrite <- Hq. symmetry. exact Hr.
  - rewrite sr_get_set_other by exact Hne. reflexivity.
Qed.

(* Regions dropped. *)
Lemma lh_drop : forall E ss ms rs,
  st_ok_pi segs VAL E ss ms -> submem rs (ss_mem ss) -> regions_wf rs = true ->
  st_ok_pi segs VAL E (mkSS (ss_pc ss) (ss_regs ss) rs (ss_resv ss) (ss_facts ss)) ms.
Proof.
  intros E ss ms rs HS Hs Hw. unfold st_ok_pi, abs_ss in *.
  exact (st_ok_submem segs E (setpc ss (BASE + ss_pc ss)) ms rs HS Hs Hw).
Qed.

(* A region added. *)
Lemma lh_add : forall E ss ms r,
  st_ok_pi segs VAL E ss ms -> region_wf r = true -> region_ok segs E (ms_mem ms) r -> all_disjoint E r (ss_mem ss) ->
  st_ok_pi segs VAL E (mkSS (ss_pc ss) (ss_regs ss) (r :: ss_mem ss) (ss_resv ss) (ss_facts ss)) ms.
Proof.
  intros E ss ms r HS Hw Hr Hd. unfold st_ok_pi, abs_ss, setpc, st_ok, mem_ok in *.
  cbn [ss_pc ss_regs ss_fregs ss_mem ss_resv ss_facts] in *.
  destruct HS as (H1 & H2 & H3 & H4 & H5 & H6 & H7 & (M1 & M2 & M3) & H9).
  refine (conj H1 (conj H2 (conj H3 (conj H4 (conj H5 (conj H6 (conj H7 (conj _ H9)))))))).
  split; [cbn [regions_wf]; rewrite Hw, M1; reflexivity|].
  split; [constructor; [exact Hr | exact M2] | cbn [pairwise_disjoint]; exact (conj Hd M3)].
Qed.
End sst.

Lemma lh_agree_extK : forall E0 E K ws, (512 <= K)%nat -> env_agree 512 E0 E -> env_agree 512 E0 (extK E K ws).
Proof.
  intros E0 E K ws HK [H1 H2]. destruct (env_agree_extK E K ws) as [A1 A2].
  split; [intros n Hn; rewrite (A1 n ltac:(lia)); exact (H1 n Hn) | rewrite A2; exact H2].
Qed.

(* One run to the pc stop, or to the next branch the engine cannot decide. *)
Ltac lh_step SH stop :=
  lazymatch goal with
  | HS : st_ok_pi _ _ ?E ?ss (restrict (w_H ?W) ?ms) |- SRr _ _ (mkCfg _ ?md) ?Q =>
    let K := eval vm_compute in (run_K A_LIM lh_Bx SH ss) in
    let rr := eval vm_compute in (sym_run_toN_pi_tok transport_tpi transport_tw K lh_Bx lh_Bspan SH FUEL stop ss) in
    lazymatch rr with
    | (?st', ?res) =>
      lazymatch goal with
      | HSH : sh_ok _ _ _ E _, HEI : img_env _ _ E, HAG : env_agree 512 ?E0 E |- _ =>
        apply (lh_run lh_Bx lh_Bspan SH W E ss ms md K stop st' res Q ltac:(unfold A_LIM; lia) HEI HS HSH
                 ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) I
                 ltac:(apply Forall_nil) ltac:(vm_compute; reflexivity));
        clear HS HSH HEI;
        let ws := fresh "ws" in let msn := fresh "ms" in let mat := fresh "mat" in
        let Hlen := fresh "Hlen" in let Hm := fresh "Hmem" in
        intros ws msn mat Hlen HEI HS HSH Hm;
        rewrite ?wvb_collapse;
        apply (lh_agree_extK E0 E K ws ltac:(lia)) in HAG
      end
    end
  end.

(* The value of register r in the machine state of a symbolic state HS: its symbolic value, computed, then tac. *)
Ltac lh_reg HS r v H tac :=
  lazymatch type of HS with
  | st_ok_pi _ _ ?Ex ?ssx (restrict ?Hh ?msx) =>
      let e := eval vm_compute in (sr_get (ss_regs ssx) r) in
      assert (H : YK11.getr (ms_regs msx) r = v) by
        (refine (eq_trans (st_ok_pi_restrict_reg Hh Ex ssx msx r HS) _); change (sv_denot Ex e = v); tac)
  end.

(* Register r of the symbolic state set to v, whose value it has (Q). *)
Ltac lh_pin_reg r v Q :=
  lazymatch goal with HS : st_ok_pi _ _ ?E _ _ |- _ =>
    let HSq := fresh "HSq" in
    pose proof (lh_pin E _ _ r v HS Q ltac:(vm_compute; reflexivity)) as HSq;
    clear HS; cbn [sh_ss ss_pc ss_regs ss_mem ss_resv ss_facts] in HSq; rename HSq into HS
  end.

(* The machine state at the stop: its shape and its memory. *)
Ltac lh_shape :=
  lazymatch goal with HS : st_ok_pi _ _ _ _ _ |- _ => pmkst HS end;
  repeat match goal with H : ms_mem ?a = ms_mem ?b |- _ => rewrite H end;
  cbn [ms_mem YK11.mkst].

(* The registers the segment keeps and the arm's cut reads: sp, gp, tp, s0, s1, s2, s4, s5, s10, s9, s11. *)
Definition lh_kp : list (bv 5) :=
  [2%bv; 3%bv; 4%bv; 8%bv; 9%bv; 18%bv; 20%bv; 21%bv; 26%bv; Z_to_bv 5 25; Z_to_bv 5 27].
Ltac lh_kin := unfold lh_kp; cbn [In]; repeat (first [left; reflexivity | right]).

Section ag. Context {rc : YM05.RunCeil}.
Lemma lh_agree32 : forall (r : bvmap 5 word) extra E,
  env_agree 512 (Eimg (PI := PI_transport) (Ereg r extra)) E -> env_agree 32 (Ereg r extra) E.
Proof.
  intros r extra E [H1 H2]. split.
  - intros n Hn. rewrite (H1 n ltac:(lia)). apply Eimg_low. unfold A_TEXT. lia.
  - rewrite H2. reflexivity.
Qed.
End ag.

(* The registers of l the run kept, from the entry registers r0 (env Eimg (Ereg r0 ex)). *)
Ltac lh_kr r0 ex l KR :=
  lazymatch goal with
  | HS : st_ok_pi _ _ ?Ex ?ssx (restrict (w_H ?Wx) ?msx), HAG : env_agree 512 _ ?Ex |- _ =>
    pose proof (regs_kept_of_st_ok_pi Ex ssx (restrict (w_H Wx) msx) r0 ex l HS (lh_agree32 r0 ex Ex HAG)
      ltac:(vm_compute; reflexivity)) as KR
  end.

Lemma lh_den : forall E0 E n v c, env_agree 512 E0 E -> (n < 512)%nat -> ew E0 n = w64 v -> 0 <= v < 2 ^ 64 ->
  sv_denot E (SOff n c) = w64 (v + c).
Proof.
  intros E0 E n v c [HA _] Hn H Hv. cbn [sv_denot]. rewrite (HA n Hn), H.
  unfold w64. rewrite unsigned_lit_small by lia. reflexivity.
Qed.

(* a0 at `bltu s6, a0` (+0x440), as the engine leaves it: the op byte (atom 32) minus 9 * ((byte * 57) >> 9), the
   low byte (+0x41c .. +0x438). It is the byte mod 9 for every byte (lh_a0_chk, all 256 values). *)
Definition lh_a0e : sv :=
  SAlu ALU_AND
    (SAlu ALU_SUB
       (SAlu ALU_SUB (SOff 32 0) (SAlu ALU_SRL (SMd M_MUL (SOff 32 0) (SLit 57)) (SLit 9)))
       (SAlu ALU_SLL (SAlu ALU_SRL (SMd M_MUL (SOff 32 0) (SLit 57)) (SLit 9)) (SLit 3)))
    (SLit 255).
Definition lh_a0f (x : word) : word := sv_denot {| ew := fun _ => x; ed := fun _ => [] |} lh_a0e.
Lemma lh_a0_chk :
  forallb (fun k => Z.eqb (bv_unsigned (lh_a0f (w64 k))) (k mod 9)) (map Z.of_nat (seq 0 256)) = true.
Proof. vm_compute. reflexivity. Qed.
Lemma lh_mod9 : forall E b, ew E 32 = w64 b -> 0 <= b < 256 -> sv_denot E lh_a0e = w64 (b mod 9).
Proof.
  intros E b H Hb.
  assert (HF : sv_denot E lh_a0e = lh_a0f (ew E 32)) by reflexivity.
  rewrite HF, H.
  pose proof lh_a0_chk as C. rewrite forallb_forall in C.
  specialize (C b ltac:(apply in_map_iff; exists (Z.to_nat b); split; [lia | apply in_seq; lia])).
  apply Z.eqb_eq in C. pose proof (Z.mod_pos_bound b 9 ltac:(lia)) as Hm.
  apply bv_eq. rewrite C. unfold w64. rewrite unsigned_lit_small by lia. reflexivity.
Qed.

Section head. Context {rc : YM05.RunCeil}.
Variable B : asyms.
Variable MT : ameter_ops.
Variable XL : Z -> Z.
Variables RLO RHI : Z.
Local Abbreviation segs := tfibsegs.
Local Abbreviation VAL := (@pa_val _ transport_listing PI_transport).
Local Abbreviation BASE := (@pa_val _ transport_listing PI_transport A_TEXT).

Lemma lh_ew_reg : forall (r : bvmap 5 word) extra n (x : bv 5), (n < 32)%nat -> Z.of_nat n = bv_unsigned x ->
  ew (Eimg (PI := PI_transport) (Ereg r extra)) n = YK11.getr r x.
Proof. intros r extra n x Hn Hx. rewrite Eimg_low by (unfold A_TEXT; lia). apply ew_Ereg_nat. exact Hx. Qed.

Lemma lh_chunk1 : forall (E : env) (m : word -> option byte) (k : nat) (b o a v : Z),
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

(* A byte of TRANS_RO_RD read through trans_rom_view_rd (notice_seg_lib.v nt_rom_mbyte). *)
Lemma lh_rom_mbyte : forall (W : world segs) m a v,
  trans_rom_view_rd W m -> trans_in_ro_rd a ->
  option_map (fun b : byte => bv_unsigned b) (YK11.seg_rom segs (Z_to_bv 64 a)) = Some v -> 0 <= v < 256 ->
  mbyte segs (mrestrict (w_H W) m) a = Some (Z_to_bv 8 v).
Proof.
  intros W m a v HRO Ha Hv Hr. pose proof (HRO a Ha) as H. rewrite Hv in H. unfold aview in H.
  destruct (mbyte segs (mrestrict (w_H W) m) a) as [x|]; [|discriminate H].
  cbn [option_map] in H. injection H as H. f_equal. rewrite <- H. symmetry. apply Z_to_bv_bv_unsigned.
Qed.

Lemma lh_jtw_rng : forall i, (i < 8)%nat -> 0 <= lh_jtw i < 2 ^ 31.
Proof.
  intros i Hi. unfold lh_jtw, transport_text, TRANS_JT_LLVMF, LO_ARMS.
  do 8 (destruct i as [|i]; [cbn [nth]; lia|]). lia.
Qed.

(* The table's 32 bytes in the image, decided against the loaded segments: entry k / 4, byte k mod 4. *)
Lemma lh_jt_rom : forall k, (k < 32)%nat ->
  option_map (fun b : byte => bv_unsigned b) (YK11.seg_rom segs (Z_to_bv 64 (TRANS_JT_LLVMF + Z.of_nat k))) =
  Some (le_byte (lh_jtw (k / 4)) 4 (k mod 4)).
Proof. intros k Hk. do 32 (destruct k as [|k]; [vm_compute; reflexivity|]). lia. Qed.

Lemma lh_jt_in : forall a, TRANS_JT_LLVMF <= a < TRANS_JT_LLVMF + 32 -> trans_in_ro_rd a.
Proof.
  intros a Ha. unfold trans_in_ro_rd. apply Exists_exists. exists (TRANS_JT_LLVMF, 32).
  split; [unfold TRANS_RO_RD; cbn [app In]; left; reflexivity | unfold in_zr; cbn [fst snd]; exact Ha].
Qed.

Lemma lh_jt_val : forall (W : world segs) m (i : nat), (i < 8)%nat -> trans_rom_view_rd W m ->
  val_mem segs (mrestrict (w_H W) m) (TRANS_JT_LLVMF + 4 * Z.of_nat i) 4 (lh_jtw i).
Proof.
  intros W m i Hi HRO j Hj.
  replace (TRANS_JT_LLVMF + 4 * Z.of_nat i + Z.of_nat j) with (TRANS_JT_LLVMF + Z.of_nat (4 * i + j)) by lia.
  apply (lh_rom_mbyte W m _ (le_byte (lh_jtw i) 4 j) HRO).
  - apply lh_jt_in. unfold TRANS_JT_LLVMF. lia.
  - rewrite (lh_jt_rom (4 * i + j) ltac:(lia)).
    replace ((4 * i + j) / 4)%nat with i by (apply (Nat.div_unique _ 4 i j); lia).
    replace ((4 * i + j) mod 4)%nat with j by (apply (Nat.mod_unique _ 4 i j); lia).
    reflexivity.
  - unfold le_byte. apply Z.mod_pos_bound. lia.
Qed.

Lemma lh_jt_ok : forall (W : world segs) m E,
  bv_unsigned (ew E (A_OBJ 11)) = TRANS_JT_LLVMF -> trans_rom_view_rd W m ->
  region_ok segs E (mrestrict (w_H W) m) lh_rg_jt.
Proof.
  intros W m E U11 HRO.
  unfold lh_rg_jt, region_ok.
  cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
  rewrite U11. split; [unfold TRANS_JT_LLVMF; lia|]. split; [unfold TRANS_JT_LLVMF; lia|].
  split; [intros o Ho; lia|].
  apply Forall_forall. intros ch Hch. apply in_map_iff in Hch. destruct Hch as (i & <- & Hi).
  apply in_seq in Hi. pose proof (lh_jtw_rng i ltac:(lia)) as Hr.
  apply (chunk_ok_val segs E _ _ (4 * Z.of_nat i) 4 (SLit (lh_jtw i)) (lh_jtw i)); [reflexivity | | lia |].
  - change (8 * Z.of_N 4) with 32. lia.
  - exact (lh_jt_val W m i ltac:(lia) HRO).
Qed.

(* lc_core across a run that writes no memory, keeps the registers of lh_kp and replaces the model's materialized
   part. *)
Lemma lh_core_kept : forall cx ly' S' (W' : world segs) regs' mem' md' e regs2 X,
  AR_laws segs B ->
  @lc_core rc B cx ly' S' W' regs' mem' md' e ->
  (forall r, In r lh_kp -> YK11.getr regs2 r = YK11.getr regs' r) ->
  @lc_core rc B cx ly' S' W' regs2 mem' (with_vm_backing (m_vm_lazy md') X md') e.
Proof.
intros cx ly' S' W' regs' mem' md' e regs2 X LAWS HC KR.
destruct HC as (HJ & Hfr & HlyF & HP & R2 & R8 & R9 & R3 & R4 & Hrest).
split.
{ eapply ajournal_gx_materialize;
    first [exact LAWS | exact transport_segs_low | exact (@pa_segs_low _ transport_listing PI_transport) | exact HJ]. }
split; [exact Hfr|]. split; [exact HlyF|]. split; [exact HP|].
split; [etransitivity; [apply KR; lh_kin | exact R2]|].
split; [etransitivity; [apply KR; lh_kin | exact R8]|].
split; [etransitivity; [apply KR; lh_kin | exact R9]|].
split; [etransitivity; [apply KR; lh_kin | exact R3]|].
split; [etransitivity; [apply KR; lh_kin | exact R4]|].
exact Hrest.
Qed.

(* The arm's cut from the head's facts, at the registers the run leaves: the kept ones, s6 = 7, s8 / s7 the cursor
   after the op byte. *)
Lemma lh_close : forall (cx : lcx) (op : lop) ly' S' (W' : world segs) regs' mem' md' e regs2 X o,
  AR_laws segs B ->
  @lc_lcore rc B MT cx op false false (lo_k op) ly' S' W' regs' mem' md' e ->
  lc_tw W' mem' (lo_B op) ->
  lc_cur cx regs' 25 27 (lo_c op) ->
  YK11.getr regs' 20 = w64 LF_S4 ->
  (forall r, In r lh_kp -> YK11.getr regs2 r = YK11.getr regs' r) ->
  YK11.getr regs2 22 = w64 7 ->
  YK11.getr regs2 (Z_to_bv 5 24) = w64 (l_p cx + TOP.fi_off (lo_c op) + 1) ->
  YK11.getr regs2 (Z_to_bv 5 23) = w64 (TOP.fi_n (lo_c op) - 1) ->
  TOP.fi_n (lo_c op) <> 0 ->
  o = lc_opc (l_pl cx) (lo_c op) ->
  @lc_st_arm rc B MT cx op o W' (lc_cfg cx (lo_arm o) regs2 mem' (with_vm_backing (m_vm_lazy md') X md')).
Proof.
intros cx op ly' S' W' regs' mem' md' e regs2 X o LAWS HL Htw (R25 & R27) R20 KR R22 R24 R23 Hn0 Ho.
destruct HL as (HC & (R18 & R26) & HSP & HFSH & HOK & He & HM & R21).
exists ly', S', regs2, mem', (with_vm_backing (m_vm_lazy md') X md'), e.
split; [reflexivity|]. split; [exact Ho|].
split.
{ split; [exact (lh_core_kept cx ly' S' W' regs' mem' md' e regs2 X LAWS HC KR)|].
  split; [split; [etransitivity; [apply KR; lh_kin | exact R18] | etransitivity; [apply KR; lh_kin | exact R26]]|].
  split; [exact HSP|]. split; [exact HFSH|]. split; [exact HOK|]. split; [exact He|]. split; [exact HM|].
  etransitivity; [apply KR; lh_kin | exact R21]. }
split; [exact Htw|].
split; [split; [etransitivity; [apply KR; lh_kin | exact R25] | etransitivity; [apply KR; lh_kin | exact R27]]|].
split.
{ unfold lc_cur, lc_oc, TOP.fuzz_u8_m. rewrite (proj2 (Z.eqb_neq _ _) Hn0). cbn [fst TOP.fi_off TOP.fi_n].
  split; [rewrite R24; f_equal; lia | rewrite R23; reflexivity]. }
split; [etransitivity; [apply KR; lh_kin | exact R20] | exact R22].
Qed.

(* Arm o in 0 .. 7 at offset arm: a0 = o pinned (Q10), the table's region in place of the byte's (HRO: the table at
   W, m reads as the image), the run to `jr a0` (+0x45c), the target pinned as a code pointer, the run to the arm. *)
Ltac lh_arm_jt o arm Q10 W m HRO :=
  lh_pin_reg (Z_to_bv 5 10) (SLit o) Q10;
  lazymatch goal with HS : st_ok_pi _ _ ?E _ _ |- _ =>
    let HSq := fresh "HSq" in
    pose proof (lh_drop E _ _ [] HS ltac:(apply submem_nil) eq_refl) as HSq; clear HS;
    cbn [sh_ss ss_pc ss_regs ss_mem ss_resv ss_facts] in HSq; rename HSq into HS
  end;
  lazymatch goal with HS : st_ok_pi _ _ ?E _ (restrict _ ?ms), HEI : img_env _ _ ?E |- _ =>
    let UJ := fresh "UJ" in let HRJ := fresh "HRJ" in let HSq := fresh "HSq" in
    assert (UJ : bv_unsigned (ew E (A_OBJ 11)) = TRANS_JT_LLVMF)
      by (rewrite (HEI (A_OBJ 11) ltac:(unfold A_OBJ, A_TEXT, A_LIM; lia)); vm_compute; reflexivity);
    assert (HRJ : region_ok segs E (ms_mem (restrict (w_H W) ms)) lh_rg_jt)
      by (cbn [ms_mem restrict]; repeat (match goal with H : ms_mem ?a = ms_mem ?b |- _ => rewrite H end);
          cbn [ms_mem YK11.mkst]; exact (lh_jt_ok W m E UJ HRO));
    pose proof (lh_add E _ _ lh_rg_jt HS ltac:(vm_compute; reflexivity) HRJ I) as HSq; clear HS;
    cbn [sh_ss ss_pc ss_regs ss_mem ss_resv ss_facts] in HSq; rename HSq into HS
  end;
  lh_step lh_SH arm;
  lazymatch goal with HS : st_ok_pi _ _ ?E _ _, HEI : img_env _ _ ?E |- _ =>
    let QJ := fresh "QJ" in
    lh_reg HS (Z_to_bv 5 10) (Z_to_bv 64 (BASE + arm)) QJ
      ltac:(cbn [sv_denot]; rewrite (HEI 252%nat ltac:(unfold A_TEXT, A_LIM; lia)); f_equal; vm_compute; reflexivity);
    lh_pin_reg (Z_to_bv 5 10) (SOff A_TEXT arm) (eq_trans QJ (eq_sym (codeptr_val E arm HEI)))
  end;
  lh_step lh_SH arm.

(* The run's end at arm o: the kept registers (from r0, ex), s6 = 7, s8 / s7 from X25 / X27, then FIN. *)
Ltac lh_finish o FIN r0 ex X25 X27 Ho :=
  lazymatch type of X25 with ew _ _ = w64 ?v25 =>
  lazymatch type of X27 with ew _ _ = w64 ?v27 =>
  lazymatch goal with HAG : env_agree 512 _ _ |- _ =>
    let KR := fresh "KR" in let Q22 := fresh "Q22" in let Q24 := fresh "Q24" in let Q23 := fresh "Q23" in
    lh_kr r0 ex lh_kp KR;
    lazymatch goal with HS : st_ok_pi _ _ _ _ _ |- _ =>
      lh_reg HS (22%bv : bv 5) (w64 7) Q22 ltac:(reflexivity);
      lh_reg HS (Z_to_bv 5 24) (w64 (v25 + 1)) Q24
        ltac:(exact (lh_den _ _ 25 v25 1 HAG ltac:(lia) X25 ltac:(lia)));
      lh_reg HS (Z_to_bv 5 23) (w64 (v27 - 1)) Q23
        ltac:(rewrite (lh_den _ _ 27 v27 (-1) HAG ltac:(lia) X27 ltac:(lia)); f_equal; lia)
    end;
    lh_shape;
    apply SRr_ret; exists o;
    exact (FIN o _ _ KR Q22 Q24 Q23 Ho)
  end end end.

(* HEAD, +0x408 .. +0x45c (and the op byte's slow path +0x132c .. +0x1330): the checked load of the op byte at s9
   (the token engine decides the check from the shadow entry of the byte, range_addressable of the input block), the
   byte mod 9 in a0, `bltu s6, a0` to arm 8, else the table entry (K1: the table reads as the image) and `jr a0`. *)
Lemma lc_head_ok : @lc_rom_view_stmt rc B MT XL RLO RHI -> @lc_head_stmt rc B MT XL RLO RHI.
Proof.
intros K1 HP cx op W' c' HB HH.
destruct HH as (ly' & S' & regs' & mem' & md' & e & -> & HL & Htw & (R25 & R27) & R20 & R22).
pose proof HL as (HC & (R18 & R26) & HSP & HFSH & HOK & He & HM & R21).
pose proof HOK as (Hag & Hops & (Hoff & Hn & Hlen) & Hn0 & Hk).
pose proof (lc_geom B MT XL RLO RHI cx ly' S' W' regs' mem' md' e HB HC) as G.
destruct G as [HAR _ _ _ _ _ (Hn26 & Hnl) HIN _].
pose proof HC as (HJ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & (HG & _)).
pose proof (@lp_laws rc B MT XL RLO RHI HP) as LAWS.
set (D := l_pl cx) in *. set (p := l_p cx) in *. set (c := lo_c op) in *.
set (off := TOP.fi_off c) in *. set (nr := TOP.fi_n c) in *.
assert (Hn1 : 1 <= nr) by lia.
assert (Hoffn : off + 1 <= l_n cx) by lia.
assert (Hl0 : 0 < l_n cx) by lia.
pose proof (HIN Hl0) as Hin.
destruct (al_blocks _ _ LAWS _ _ _ _ _ _ _ HAR Hin) as (_ & Hp4096 & Hpceil & Happ & _).
pose proof (req_size_pos (l_n cx) ltac:(lia)) as (Hq1 & Hq2).
assert (Hceil : p + l_n cx <= 140737479966720)
  by (pose proof (@alloc_ceiling_value rc) as (Hac & _); lia).
(* the op byte *)
assert (Hj : (Z.to_nat off < length (map (fun b : byte => bv_unsigned b) D))%nat) by (rewrite length_map; lia).
destruct (HG _ Hj) as (Vb & Rb).
set (b := nth (Z.to_nat off) (map (fun b : byte => bv_unsigned b) D) 0) in *.
replace (p + Z.of_nat (Z.to_nat off)) with (p + off) in Vb by lia.
set (E0 := Eimg (PI := PI_transport) (Ereg regs' [w64 b])).
assert (U25 : bv_unsigned (ew E0 25) = p + off)
  by (unfold E0; rewrite (lh_ew_reg regs' _ 25 (Z_to_bv 5 25) ltac:(lia) eq_refl), R25; unfold w64;
      apply unsigned_lit_small; lia).
assert (U26 : bv_unsigned (ew E0 26) = SHADOW_OFF)
  by (unfold E0; rewrite (lh_ew_reg regs' _ 26 26%bv ltac:(lia) eq_refl), R26; unfold w64;
      apply unsigned_lit_small; unfold SHADOW_OFF; lia).
assert (X32 : ew E0 32 = w64 b) by (unfold E0; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs' _ 0)).
assert (U32 : bv_unsigned (ew E0 32) = b) by (rewrite X32; unfold w64; apply unsigned_lit_small; lia).
assert (HS : st_ok_pi (fx := l_fx cx) segs VAL E0 lh_ss
  (restrict (w_H W') (@YK11.mkst (l_fx cx) regs' (Z_to_bv 64 (BASE + LO_HEAD)) mem' (YK11.seg_rom segs)))).
{ rewrite restrict_mkst_fx. unfold lh_ss.
  apply (@pa_entry_st_ok_full (l_fx cx) rc transport_listing PI_transport).
  - apply regs_ok_Eimg_Ereg.
  - vm_compute. reflexivity.
  - apply Forall_cons; [|apply Forall_nil]. unfold lh_rg, YP09.region_ok.
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val]. rewrite U25.
    split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
    apply Forall_cons; [|apply Forall_nil].
    apply (lh_chunk1 _ _ 32 (p + off) 0 (p + off) b); [exact X32 | lia | lia | exact Vb].
  - exact (conj I I).
  - unfold facts_ok, lh_G. cbn [f_atoms f_conds f_alias atoms_ok conds_ok alias_ok].
    unfold afact_ok, lh_PTRHI. cbn [af_lo af_hi af_al2].
    rewrite U26, U25, U32. rewrite !Z.pow_0_r, !Z.mod_1_r. unfold SHADOW_OFF.
    repeat split; try exact I; lia. }
assert (HRA : range_addressable (aview segs (w_H W') mem') SHADOW_OFF p (l_n cx))
  by (apply (range_addressable_of_block segs B LAWS ly' S' W' mem' md' p (l_n cx) p (l_n cx) HAR Hin); lia).
assert (HSH : sh_ok segs lh_Bx lh_SH E0 (mrestrict (w_H W') mem')).
{ apply Forall_cons; [|apply Forall_nil].
  apply (shent_ok_of_range segs (w_H W') mem' E0 lh_Bx 25%nat p (l_n cx) (p + off) 0 1).
  - exact HRA.
  - unfold lh_Bx. apply U_atom; [|unfold SHADOW_OFF; lia].
    unfold E0. rewrite (lh_ew_reg regs' _ 26 26%bv ltac:(lia) eq_refl). exact R26.
  - apply U_atom; [|lia].
    unfold E0. rewrite (lh_ew_reg regs' _ 25 (Z_to_bv 5 25) ltac:(lia) eq_refl). exact R25.
  - lia.
  - lia.
  - intros x Hx. cbn [Z.min Z.max] in Hx. unfold in_app in Happ.
    destruct Happ as (_ & [Ha | (Ha1 & Ha2)]); unfold kLowShadowBeg, kHighMemBeg, ASAN_CEIL, SHADOW_OFF in *; lia. }
assert (HEI : img_env VAL A_LIM E0) by apply Eimg_env.
pose proof (env_agree_refl 512 E0) as HAG.
assert (X25 : ew E0 25 = w64 (p + off))
  by (unfold E0; rewrite (lh_ew_reg regs' _ 25 (Z_to_bv 5 25) ltac:(lia) eq_refl); exact R25).
assert (X27 : ew E0 27 = w64 nr)
  by (unfold E0; rewrite (lh_ew_reg regs' _ 27 (Z_to_bv 5 27) ltac:(lia) eq_refl); exact R27).
(* the op code: the byte mod 9 *)
assert (Hopc : lc_opc D c = b mod 9).
{ unfold lc_opc, TOP.fuzz_u8_m.
  replace (TOP.fi_n c =? 0) with false by (symmetry; apply Z.eqb_neq; exact Hn0).
  cbn [snd]. unfold DSpec.at8, DSpec.bz, b. f_equal.
  rewrite (nth_indep _ 0 (bv_unsigned (DSpec.b8 0)) Hj). rewrite map_nth. reflexivity. }
(* K1: the table reads as the image *)
assert (HRO : trans_rom_view_rd W' mem') by exact (K1 HP cx ly' S' W' regs' mem' md' e HB HC).
unfold lc_cfg.
lazymatch goal with |- SRr _ ?Wx _ ?Q =>
  change (SRr segs Wx (mkCfg (@YK11.mkst (l_fx cx) regs' (Z_to_bv 64 (BASE + LO_HEAD)) mem' (YK11.seg_rom segs)) md') Q)
end.
set (fx := l_fx cx) in *.
(* s6 = 7 as a literal, so the engine decides `bltu s6, a0` once a0 is a literal *)
lh_pin_reg (22%bv : bv 5) (SLit 7) R22.
(* +0x408 .. +0x440: the checked load (the slow path +0x132c decided by lh_SH), the byte, a0 = byte mod 9 *)
lh_step lh_SH 0x6e8.
lazymatch goal with HAG : env_agree 512 _ ?Ex |- _ =>
  lh_reg HS (Z_to_bv 5 10) (w64 (b mod 9)) Q10
    ltac:(exact (lh_mod9 Ex b (eq_trans (proj1 HAG 32%nat ltac:(lia)) X32) Rb))
end.
pose proof (Z.mod_pos_bound b 9 ltac:(lia)) as Hm9.
(* the arm's cut from the head's facts, at the registers the run leaves *)
assert (FIN : forall o regs2 X,
  (forall r, In r lh_kp -> YK11.getr regs2 r = YK11.getr regs' r) ->
  YK11.getr regs2 22 = w64 7 ->
  YK11.getr regs2 (Z_to_bv 5 24) = w64 (p + off + 1) ->
  YK11.getr regs2 (Z_to_bv 5 23) = w64 (nr - 1) ->
  b mod 9 = o ->
  @lc_st_arm rc B MT cx op o W' (lc_cfg cx (lo_arm o) regs2 mem' (with_vm_backing (m_vm_lazy md') X md'))).
{ intros o regs2 X KR Q22 Q24 Q23 Ho.
  exact (lh_close cx op ly' S' W' regs' mem' md' e regs2 X o LAWS HL Htw (conj R25 R27) R20 KR Q22 Q24 Q23 Hn0
           (eq_trans (eq_sym Ho) (eq_sym Hopc))). }
assert (Hcase : b mod 9 = 0 \/ b mod 9 = 1 \/ b mod 9 = 2 \/ b mod 9 = 3 \/ b mod 9 = 4 \/ b mod 9 = 5 \/
                b mod 9 = 6 \/ b mod 9 = 7 \/ b mod 9 = 8) by lia.
destruct Hcase as [Ho|[Ho|[Ho|[Ho|[Ho|[Ho|[Ho|[Ho|Ho]]]]]]]]; rewrite Ho in Q10.
- lh_arm_jt 0 0x460 Q10 W' mem' HRO. lh_finish 0 FIN regs' [w64 b] X25 X27 Ho.
- lh_arm_jt 1 0x5e8 Q10 W' mem' HRO. lh_finish 1 FIN regs' [w64 b] X25 X27 Ho.
- lh_arm_jt 2 0x564 Q10 W' mem' HRO. lh_finish 2 FIN regs' [w64 b] X25 X27 Ho.
- lh_arm_jt 3 0x5b4 Q10 W' mem' HRO. lh_finish 3 FIN regs' [w64 b] X25 X27 Ho.
- lh_arm_jt 4 0x48c Q10 W' mem' HRO. lh_finish 4 FIN regs' [w64 b] X25 X27 Ho.
- lh_arm_jt 5 0x618 Q10 W' mem' HRO. lh_finish 5 FIN regs' [w64 b] X25 X27 Ho.
- lh_arm_jt 6 0x684 Q10 W' mem' HRO. lh_finish 6 FIN regs' [w64 b] X25 X27 Ho.
- lh_arm_jt 7 0x5dc Q10 W' mem' HRO. lh_finish 7 FIN regs' [w64 b] X25 X27 Ho.
- (* op 8: `bltu s6, a0` taken to +0x6e8 *)
  lh_pin_reg (Z_to_bv 5 10) (SLit 8) Q10. lh_step lh_SH 0x6e8. lh_finish 8 FIN regs' [w64 b] X25 X27 Ho.
Qed.

End head.

Print Assumptions lc_head_ok.
