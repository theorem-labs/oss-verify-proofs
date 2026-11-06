(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: restates text of projects/cgif/cgif_file_fuzzer/proofs/lib/YCbq.v:528-543, 616-634;
   projects/cgif/cgif_rgb_fuzzer/proofs/lib/YC05.v:41-45, 208-214, 230-234, for libreac/fuzz_identity's asan-ubsan build
   (lib/B). The same text also appears in projects/cgif/cgif_file_fuzzer/proofs/lib/YCbo.v:420-423, 430-444, 447-448,
   453-455, 470-475, 477-486, 489-491, 502-505, 511-514, 1255-1258. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_identity/lib/B/Prog/reac_box_name_seg_rel.v, with its module paths, module names and numbers changed; 274 of its 316 lines of code are new or changed and 1882 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libdiginet/fuzz_transport/lib/A/Prog/DgnBcRel.v, with its module paths and module names changed; 548 of its 585 lines of code are new or changed and 279 lines of the source are left out. *)
(* LLVMFuzzerTestOneInput_seg_head: proves no function (kind: segment lemma of LLVMFuzzerTestOneInput's walk, image B).
   lc_head_ok : lc_rom_view_stmt -> lc_head_stmt (lib/B/Prog/LLVMFuzzerTestOneInput_segs.v), the segment HEAD of the
   image-B walk of fuzz_transport.asan-ubsan's LLVMFuzzerTestOneInput, +0x58c .. +0x5f0 of the listing
   lib/B/Prog/DgnTransportBList.v (slot k at 0x812a0 + 4 k), from the loop head (lc_st_head) to the first instruction
   of arm o (lc_st_arm), o = the op byte mod 9. It writes no memory and calls nothing:
     +0x58c .. +0x594  s8 = s9 + 1 and the UBSan cursor test `bltu s6, s8` (s6 = 1, s9 = p + off >= 4096: taken,
                       so the trap edge 0x81834 to the trap word +0x1b44 is not taken);
     +0x598 .. +0x5a8  the shadow byte of s9 (the cursor) and `beqz a0`, else `j` to the slow path +0x16b8 .. +0x16c0
                       (`andi a1, s9, 7`, `bge a1, a0` to the report call +0x1c60 .. +0x1c64, else `j` back);
     +0x5ac .. +0x5cc  the op byte (`lbu a0, 0(s9)`), a0 = byte - 9 * ((byte * 57) >> 9) (the low byte),
                       s11 = s7 - 1;
     +0x5d0 .. +0x5d4  a1 = 7, `bltu a1, a0` to arm 8 at +0x90c;
     +0x5d8 .. +0x5f0  the table entry at TRANS_JT_LLVMF + 4 * a0 (`lw`, the table's address from the listing's
                       object 11) plus the table's address, `jr a0` to arm a0.
   How it is proved. The PA engine runs from a symbolic state with two read-only regions: the op byte at s9 (atom 32)
   and the shadow byte of s9 (atom 34) at its shadow address (atom 33, named by the alias fact (s9 >> 3) + s10). The
   shadow byte comes from range_addressable of the input block (YCbq.v range_addressable_of_block): it is 0, or in
   (0, 8) and above s9 mod 8. s6 is pinned to the literal 1, so the engine decides the UBSan cursor test. The run stops
   at `beqz a0`, which is split (DgnTransportBPaLib.v paj_branch): when the shadow byte is 0 the run goes on to
   `bltu a1, a0`; else it takes the slow path and stops at `bge a1, a0`, whose taken side is refuted by the shadow
   byte's bound (lh_bge), and its other side goes back to the op byte and on to `bltu a1, a0`. There a0 is the byte
   mod 9 for each of the 256 bytes (lh_mod9); after the case split on it, a0 is pinned to the literal op code, so the
   engine decides `bltu`. For ops 0 .. 7 both regions are dropped and the table's added (its 32 bytes read as the image
   by K1, lc_rom_view_stmt, and decided against the loaded segments, lh_jt_rom); the run stops at `jr a0`, the target
   is pinned as the code pointer of the arm and a last run takes the jump. Every run writes no memory, so lc_core is
   kept with the model's materialized part replaced (W_journalG.v ajournal_gx_materialize, at any FP), and the
   registers the cut reads are the entry's (lh_kp). *)
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
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import
DgnTransportBSyms DgnTransportBList DgnTransportBAddr DgnTransportBPa DgnTransportBImg DgnTransportBPaLib CanKit.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B Require Import YB1v YE2k YCfn.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B Require AsanCells TransportGB YE2y.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A Require Import W_journalG.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import PaBase.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import DgnTransportBCg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import TransportGCg TWorldG.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import TWorldB TImgB.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import LLVMFuzzerTestOneInput_cg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import LLVMFuzzerTestOneInput_segs.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import LLVMFuzzerTestOneInput_st.
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

(* s10 holds the shadow base; no shadow entry: the op byte's check reads its shadow byte as a region. *)
Definition lh_Bx : sv := SOff 26 0.
Definition lh_Bspan : Z * Z := (SHADOW_OFF, SHADOW_OFF + 2 ^ 44 - 1).
Definition lh_SH : list shent := [].
Definition lh_PTRHI : Z := 140737488355324.
(* atom 25: s9 = p + off; atom 32: the op byte; atom 33: the shadow address of s9, (s9 >> 3) + s10 (the alias
   fact); atom 34: its shadow byte, in [0, 7]. *)
Definition lh_G : facts := mkFacts [(26%nat, mkAF SHADOW_OFF SHADOW_OFF 0); (25%nat, mkAF 4096 lh_PTRHI 0);
  (32%nat, mkAF 0 255 0); (33%nat, mkAF SHADOW_OFF (2 ^ 46) 0); (34%nat, mkAF 0 7 0)] []
  [(SAlu ALU_ADD (SAlu ALU_SRL (SOff 25 0) (SLit 3)) (SOff 26 0), SOff 33 0)].
Definition lh_rg : YP09.region := YP09.mkRegion (Some 25%nat) 0 1 0 0 [YP09.mkChunk 0 (CVal 1 (SOff 32 0))].
Definition lh_rg_sp : YP09.region := YP09.mkRegion (Some 33%nat) 0 1 0 0 [YP09.mkChunk 0 (CVal 1 (SOff 34 0))].
Definition lh_ss : sstate := mkSS LO_HEAD sr_atoms [lh_rg; lh_rg_sp] None lh_G.
(* The op switch's table at TRANS_JT_LLVMF (the listing's object 11, atom A_OBJ 11): entry i, read by `lw` at
   +0x5e8, is arm i's distance from the table (st.v lc_rom_tab). *)
Definition lh_jtw (i : nat) : Z := transportb_text + nth i LO_ARMS 0 - TRANS_JT_LLVMF.
Definition lh_rg_jt : YP09.region := YP09.mkRegion (Some (A_OBJ 11)) 0 32 0 0
  (map (fun i => YP09.mkChunk (4 * Z.of_nat i) (CVal 4 (SLit (lh_jtw i)))) (seq 0 8)).

(* ------------------------------------------------------------------ *)
(* One run of the engine over read-only regions                        *)
(* ------------------------------------------------------------------ *)

Section run. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Local Abbreviation segs := tfibsegs.
Local Abbreviation VAL := (@pa_val _ transportb_listing PI_transportb).

(* The run writes no memory (its regions are read-only), so the memory after it is the memory before; the model
   after it is the model before with its materialized part replaced. *)
Lemma lh_run : forall (Bx : sv) (Bspan : Z * Z) (SH : list shent) (W : world segs) (E : env) (ss : sstate)
    (ms : machine_state) (md : Model) (K : nat) (stop : Z) (st' : shst) (r : ptrun_status tbsym)
    (Q : world segs -> config -> Prop),
  (A_LIM <= K)%nat ->
  img_env VAL A_LIM E ->
  st_ok_pi segs VAL E ss (restrict (w_H W) ms) ->
  sh_ok segs Bx SH E (mrestrict (w_H W) (ms_mem ms)) ->
  sh_static_ok K Bx Bspan SH (ss_facts ss) (ss_mem ss) = true ->
  sym_run_toN_pi_tok transportb_tpi transportb_tw K Bx Bspan SH FUEL stop ss = (st', r) ->
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
  assert (Hrun' : sym_run_toN_pi_tok (ptree_of_list transportb_listing) (tw_of 0 transportb_listing)
                    K Bx Bspan SH FUEL stop ss = (st', r))
    by (rewrite (@pl_tw_eq transportb_listing PL_transportb); exact Hrun).
  destruct (sym_run_to_pi_tok_sound tbsym _ _ VAL _ transportb_listing
     (pa_fetch_ok (PI := PI_transportb)) (@pa_cert _ transportb_listing PI_transportb)
     (@pa_B_ok _ transportb_listing PI_transportb)
     A_LIM A_LIM_text (@pl_lim transportb_listing PL_transportb) (@pl_len transportb_listing PL_transportb)
     K Bx Bspan SH HK FUEL stop E ss (restrict (w_H W) ms) st' r HE HS HSH Hchk Hrun' Hobl)
   as (ws & msr' & Hlen & Hms & HE' & HP & Hsh' & _ & Hfr).
  apply (SRr_msteps segs (@pa_wx _ transportb_listing PI_transportb) W ms msr' md Q Hms).
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
Local Abbreviation VAL := (@pa_val _ transportb_listing PI_transportb).
Local Abbreviation BASE := (@pa_val _ transportb_listing PI_transportb A_TEXT).

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
    let rr := eval vm_compute in (sym_run_toN_pi_tok transportb_tpi transportb_tw K lh_Bx lh_Bspan SH FUEL stop ss) in
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

(* The branch the engine stopped at, split (DgnTransportBPaLib.v paj_branch): Hc is its test, HS the state with the
   test's side added to its facts. *)
Ltac lh_branch SH :=
  lazymatch goal with
  | HS : st_ok_pi _ _ ?E ?ss (restrict (w_H ?W) ?ms) |- SRr _ _ (mkCfg _ ?md) ?Q =>
    let K := eval vm_compute in (run_K A_LIM lh_Bx SH ss) in
    let why := psym_why_tok transportb_tpi transportb_tw K lh_Bx lh_Bspan SH (start K lh_Bx lh_Bspan SH ss) in
    lazymatch why with
    | SR_branch ?c ?a ?b =>
      apply (paj_branch (PI := PI_transportb) W E ss ms md Q c a b HS); clear HS;
      let Hc := fresh "Hc" in let HSn := fresh "HS" in intros Hc HSn
    | _ => fail "lh_branch: the state is not stuck at a branch:" why
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

(* The registers the segment keeps and the arm's cut reads: sp, gp, tp, s0, s1, s2, s3, s4, s10, s7, s9. *)
Definition lh_kp : list (bv 5) :=
  [2%bv; 3%bv; 4%bv; 8%bv; 9%bv; 18%bv; 19%bv; 20%bv; 26%bv; Z_to_bv 5 23; Z_to_bv 5 25].
Ltac lh_kin := unfold lh_kp; cbn [In]; repeat (first [left; reflexivity | right]).

Section ag. Context {rc : YM05.RunCeil}.
Lemma lh_agree32 : forall (r : bvmap 5 word) extra E,
  env_agree 512 (Eimg (PI := PI_transportb) (Ereg r extra)) E -> env_agree 32 (Ereg r extra) E.
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

(* a0 at `bltu a1, a0` (+0x5d4), as the engine leaves it: the op byte (atom 32) minus 9 * ((byte * 57) >> 9), the
   low byte (+0x5b0 .. +0x5c8). It is the byte mod 9 for every byte (lh_a0_chk, all 256 values). *)
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

(* `beqz` on a register atom m holding n: the test n = 0. *)
Lemma lh_beqz : forall E (m : nat) n b, ew E m = Z_to_bv 64 n -> 0 <= n < 2 ^ 64 ->
  branch_taken BC_EQ (sv_denot E (SOff m 0)) (sv_denot E (SLit 0)) = b -> (n =? 0) = b.
Proof.
intros E m n b Hm Hn Hb. rewrite <- Hb.
rewrite (denot_lit_U E (SOff m 0)), U_SOff, Hm, unsigned_lit_small by lia. rewrite Z.add_0_r, (zcanon_id n) by (unfold M64; lia).
change (sv_denot E (SLit 0)) with (Z_to_bv 64 0). cbn [branch_taken].
unfold bv_eqb. rewrite !Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64).
rewrite !Z.mod_small by lia. reflexivity.
Qed.

(* The slow path's `bge a1, a0` (+0x16bc) with a1 = s9 & 7 and a0 the shadow byte of s9, not 0: the shadow byte is
   above s9 mod 8 and below 8 (the input block's shadow), so the branch to the report call +0x1c60 is not taken. *)
Lemma lh_bge : forall E x sb b, ew E 25 = Z_to_bv 64 x -> ew E 34 = Z_to_bv 64 sb -> 0 <= x < 2 ^ 64 ->
  x mod 8 < sb < 8 ->
  branch_taken BC_GE (sv_denot E (SAlu ALU_AND (SOff 25 0) (SLit 7))) (sv_denot E (SOff 34 0)) = b -> b = false.
Proof.
intros E x sb b H25 H34 Hx Hsb Hb. rewrite <- Hb.
pose proof (Z.mod_pos_bound x 8 ltac:(lia)) as Hm.
rewrite (denot_lit_U E (SAlu _ _ _)), U_SAlu. cbn [zalu_raw].
rewrite U_SOff, H25, U_SLit, unsigned_lit_small by lia. rewrite Z.add_0_r, (zcanon_id x), (zcanon_id 7) by (unfold M64; lia).
assert (HL : Z.land x 7 = x mod 8) by exact (Z.land_ones x 3 ltac:(lia)).
rewrite HL.
rewrite (zcanon_id (x mod 8)) by (unfold M64; lia).
rewrite (denot_lit_U E (SOff 34 0)), U_SOff, H34, unsigned_lit_small by lia.
rewrite Z.add_0_r, (zcanon_id sb) by (unfold M64; lia).
set (z := x mod 8) in *. clearbody z.
assert (Hz7 : z = 0 \/ z = 1 \/ z = 2 \/ z = 3 \/ z = 4 \/ z = 5 \/ z = 6 \/ z = 7) by lia.
assert (Hs7 : sb = 1 \/ sb = 2 \/ sb = 3 \/ sb = 4 \/ sb = 5 \/ sb = 6 \/ sb = 7) by lia.
destruct Hz7 as [->|[->|[->|[->|[->|[->|[->| ->]]]]]]];
  destruct Hs7 as [->|[->|[->|[->|[->|[->| ->]]]]]];
  first [exfalso; lia | vm_compute; reflexivity].
Qed.

Section head. Context {rc : YM05.RunCeil}.
Variable B : asyms.
Variable MT : ameter_ops.
Variable XL : Z -> Z.
Variables RLO RHI : Z.
Local Abbreviation segs := tfibsegs.
Local Abbreviation VAL := (@pa_val _ transportb_listing PI_transportb).
Local Abbreviation BASE := (@pa_val _ transportb_listing PI_transportb A_TEXT).

Lemma lh_ew_reg : forall (r : bvmap 5 word) extra n (x : bv 5), (n < 32)%nat -> Z.of_nat n = bv_unsigned x ->
  ew (Eimg (PI := PI_transportb) (Ereg r extra)) n = YK11.getr r x.
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
  intros i Hi. unfold lh_jtw, transportb_text, TRANS_JT_LLVMF, LO_ARMS.
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
    first [exact LAWS | exact transportb_segs_low | exact (@pa_segs_low _ transportb_listing PI_transportb) | exact HJ]. }
split; [exact Hfr|]. split; [exact HlyF|]. split; [exact HP|].
split; [etransitivity; [apply KR; lh_kin | exact R2]|].
split; [etransitivity; [apply KR; lh_kin | exact R8]|].
split; [etransitivity; [apply KR; lh_kin | exact R9]|].
split; [etransitivity; [apply KR; lh_kin | exact R3]|].
split; [etransitivity; [apply KR; lh_kin | exact R4]|].
exact Hrest.
Qed.

(* The arm's cut from the head's facts, at the registers the run leaves: the kept ones, s6 = 1, s8 / s11 the cursor
   after the op byte. *)
Lemma lh_close : forall (cx : lcx) (op : lop) ly' S' (W' : world segs) regs' mem' md' e regs2 X o,
  AR_laws segs B ->
  @lc_lcore rc B MT cx op false false (lo_k op) ly' S' W' regs' mem' md' e ->
  lc_tw W' mem' (lo_B op) ->
  lc_cur cx regs' 25 23 (lo_c op) ->
  YK11.getr regs' 20 = w64 (lc_F cx + 32) ->
  (forall r, In r lh_kp -> YK11.getr regs2 r = YK11.getr regs' r) ->
  YK11.getr regs2 22 = w64 1 ->
  YK11.getr regs2 (Z_to_bv 5 24) = w64 (l_p cx + TOP.fi_off (lo_c op) + 1) ->
  YK11.getr regs2 (Z_to_bv 5 27) = w64 (TOP.fi_n (lo_c op) - 1) ->
  TOP.fi_n (lo_c op) <> 0 ->
  o = lc_opc (l_pl cx) (lo_c op) ->
  @lc_st_arm rc B MT cx op o W' (lc_cfg cx (lo_arm o) regs2 mem' (with_vm_backing (m_vm_lazy md') X md')).
Proof.
intros cx op ly' S' W' regs' mem' md' e regs2 X o LAWS HL Htw (R25 & R23) R20 KR R22 R24 R27 Hn0 Ho.
destruct HL as (HC & (R18 & R26) & HSP & HFSH & HOK & He & HM & R19).
exists ly', S', regs2, mem', (with_vm_backing (m_vm_lazy md') X md'), e.
split; [reflexivity|]. split; [exact Ho|].
split.
{ split; [exact (lh_core_kept cx ly' S' W' regs' mem' md' e regs2 X LAWS HC KR)|].
  split; [split; [etransitivity; [apply KR; lh_kin | exact R18] | etransitivity; [apply KR; lh_kin | exact R26]]|].
  split; [exact HSP|]. split; [exact HFSH|]. split; [exact HOK|]. split; [exact He|]. split; [exact HM|].
  etransitivity; [apply KR; lh_kin | exact R19]. }
split; [exact Htw|].
split; [split; [etransitivity; [apply KR; lh_kin | exact R25] | etransitivity; [apply KR; lh_kin | exact R23]]|].
split.
{ unfold lc_cur, lc_oc, TOP.fuzz_u8_m. rewrite (proj2 (Z.eqb_neq _ _) Hn0). cbn [fst TOP.fi_off TOP.fi_n].
  split; [rewrite R24; f_equal; lia | rewrite R27; reflexivity]. }
split; [etransitivity; [apply KR; lh_kin | exact R20] | exact R22].
Qed.

(* Arm o in 0 .. 7 at offset arm: a0 = o pinned (Q10), the table's region in place of the two byte regions (HRO: the
   table at W, m reads as the image), the run to `jr a0` (+0x5f0), the target pinned as a code pointer, the run to
   the arm. *)
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

(* The run's end at arm o: the kept registers (from r0, ex), s6 = 1, s8 / s11 from X25 / X23, then FIN. *)
Ltac lh_finish o FIN r0 ex X25 X23 Ho :=
  lazymatch type of X25 with ew _ _ = w64 ?v25 =>
  lazymatch type of X23 with ew _ _ = w64 ?v23 =>
  lazymatch goal with HAG : env_agree 512 _ _ |- _ =>
    let KR := fresh "KR" in let Q22 := fresh "Q22" in let Q24 := fresh "Q24" in let Q27 := fresh "Q27" in
    lh_kr r0 ex lh_kp KR;
    lazymatch goal with HS : st_ok_pi _ _ _ _ _ |- _ =>
      lh_reg HS (22%bv : bv 5) (w64 1) Q22 ltac:(reflexivity);
      lh_reg HS (Z_to_bv 5 24) (w64 (v25 + 1)) Q24
        ltac:(exact (lh_den _ _ 25 v25 1 HAG ltac:(lia) X25 ltac:(lia)));
      lh_reg HS (Z_to_bv 5 27) (w64 (v23 - 1)) Q27
        ltac:(rewrite (lh_den _ _ 23 v23 (-1) HAG ltac:(lia) X23 ltac:(lia)); f_equal; lia)
    end;
    lh_shape;
    apply SRr_ret; exists o;
    exact (FIN o _ _ KR Q22 Q24 Q27 Ho)
  end end end.

(* From `bltu a1, a0` (+0x5d4) on: a0 is the byte b mod 9 (lh_mod9), the case split on it, and each arm. *)
Ltac lh_dispatch b X32 Rb FIN r0 ex X25 X23 W m HRO :=
  lazymatch goal with HAG : env_agree 512 _ ?Ex, HS : st_ok_pi _ _ ?Ex _ _ |- _ =>
    let Q10 := fresh "Q10" in let Ho := fresh "Ho" in let Hcase := fresh "Hcase" in
    lh_reg HS (Z_to_bv 5 10) (w64 (b mod 9)) Q10
      ltac:(exact (lh_mod9 Ex b (eq_trans (proj1 HAG 32%nat ltac:(lia)) X32) Rb));
    assert (Hcase : b mod 9 = 0 \/ b mod 9 = 1 \/ b mod 9 = 2 \/ b mod 9 = 3 \/ b mod 9 = 4 \/ b mod 9 = 5 \/
                    b mod 9 = 6 \/ b mod 9 = 7 \/ b mod 9 = 8)
      by (pose proof (Z.mod_pos_bound b 9 ltac:(lia)); lia);
    destruct Hcase as [Ho|[Ho|[Ho|[Ho|[Ho|[Ho|[Ho|[Ho|Ho]]]]]]]]; rewrite Ho in Q10;
    [ lh_arm_jt 0 0x5f4 Q10 W m HRO; lh_finish 0 FIN r0 ex X25 X23 Ho
    | lh_arm_jt 1 0x7b4 Q10 W m HRO; lh_finish 1 FIN r0 ex X25 X23 Ho
    | lh_arm_jt 2 0x6e8 Q10 W m HRO; lh_finish 2 FIN r0 ex X25 X23 Ho
    | lh_arm_jt 3 0x758 Q10 W m HRO; lh_finish 3 FIN r0 ex X25 X23 Ho
    | lh_arm_jt 4 0x630 Q10 W m HRO; lh_finish 4 FIN r0 ex X25 X23 Ho
    | lh_arm_jt 5 0x7f4 Q10 W m HRO; lh_finish 5 FIN r0 ex X25 X23 Ho
    | lh_arm_jt 6 0x864 Q10 W m HRO; lh_finish 6 FIN r0 ex X25 X23 Ho
    | lh_arm_jt 7 0x7a8 Q10 W m HRO; lh_finish 7 FIN r0 ex X25 X23 Ho
    | (* op 8: `bltu a1, a0` taken to +0x90c *)
      lh_pin_reg (Z_to_bv 5 10) (SLit 8) Q10; lh_step lh_SH 0x90c; lh_finish 8 FIN r0 ex X25 X23 Ho ]
  end.

(* HEAD, +0x58c .. +0x5f0 (the op byte's slow path +0x16b8 .. +0x16c0, its report +0x1c60 .. +0x1c64 and the trap
   word +0x1b44 unreached): the UBSan cursor test (decided: s6 = 1 < s9 + 1), the checked load of the op byte at s9
   (its shadow byte a region: `beqz a0` split, the slow path's `bge a1, a0` refuted by lh_bge), the byte mod 9 in a0,
   `bltu a1, a0` to arm 8, else the table entry (K1: the table reads as the image) and `jr a0`. *)
Lemma lc_head_ok (K1 : lc_rom_view_stmt B MT XL RLO RHI) : lc_head_stmt B MT XL RLO RHI.
Proof.
intros HP cx op W' c' HB HH.
destruct HH as (ly' & S' & regs' & mem' & md' & e & -> & HL & Htw & (R25 & R23) & (R20 & R22)).
pose proof HL as (HC & (R18 & R26) & HSP & HFSH & HOK & He & HM & R19).
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
(* the shadow byte of the op byte: 0, or above (p + off) mod 8 and below 8 (range_addressable of the input block) *)
assert (HRA : range_addressable (aview segs (w_H W') mem') SHADOW_OFF p (l_n cx))
  by (apply (range_addressable_of_block segs B LAWS ly' S' W' mem' md' p (l_n cx) p (l_n cx) HAR Hin); lia).
destruct (HRA (p + off) ltac:(lia)) as (sb & Hsb & Hsok).
unfold shadow_of_addr in Hsb.
pose proof (Z.mod_pos_bound (p + off) 8 ltac:(lia)) as Hm8.
assert (Hsb7 : 0 <= sb <= 7) by (destruct Hsok as [-> | (Hs1 & Hs2)]; lia).
pose proof (Z.div_mod (p + off) 8 ltac:(lia)) as DP.
assert (HP8 : 0 <= (p + off) / 8 <= 2 ^ 44)
  by (split; [apply Z.div_pos | apply Z.div_le_upper_bound]; lia).
set (sha := SHADOW_OFF + (p + off) / 8) in *.
assert (Esha : sha = SHADOW_OFF + (p + off) / 8) by reflexivity.
pose proof (YE2y.val_mem1_of_aview (w_H W') mem' _ _ Hsb) as VS.
assert (Happx : p + off + 1 <= kLowShadowBeg \/ kHighMemBeg <= p + off).
{ unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in Happ.
  destruct Happ as (_ & [H1 | (H1 & _)]); [left; unfold kLowShadowBeg; lia | right; unfold kHighMemBeg; lia]. }
set (E0 := Eimg (PI := PI_transportb) (Ereg regs' [w64 b; w64 sha; w64 sb])).
assert (X25 : ew E0 25 = w64 (p + off))
  by (unfold E0; rewrite (lh_ew_reg regs' _ 25 (Z_to_bv 5 25) ltac:(lia) eq_refl); exact R25).
assert (X23 : ew E0 23 = w64 nr)
  by (unfold E0; rewrite (lh_ew_reg regs' _ 23 (Z_to_bv 5 23) ltac:(lia) eq_refl); exact R23).
assert (X26 : ew E0 26 = w64 SHADOW_OFF)
  by (unfold E0; rewrite (lh_ew_reg regs' _ 26 26%bv ltac:(lia) eq_refl); exact R26).
assert (X32 : ew E0 32 = w64 b) by (unfold E0; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs' _ 0)).
assert (X33 : ew E0 33 = w64 sha) by (unfold E0; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs' _ 1)).
assert (X34 : ew E0 34 = w64 sb) by (unfold E0; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs' _ 2)).
assert (U25 : bv_unsigned (ew E0 25) = p + off) by (rewrite X25; unfold w64; apply unsigned_lit_small; lia).
assert (U26 : bv_unsigned (ew E0 26) = SHADOW_OFF)
  by (rewrite X26; unfold w64; apply unsigned_lit_small; unfold SHADOW_OFF; lia).
assert (U32 : bv_unsigned (ew E0 32) = b) by (rewrite X32; unfold w64; apply unsigned_lit_small; lia).
assert (U33 : bv_unsigned (ew E0 33) = sha)
  by (rewrite X33; unfold w64; apply unsigned_lit_small; unfold SHADOW_OFF in *; lia).
assert (U34 : bv_unsigned (ew E0 34) = sb) by (rewrite X34; unfold w64; apply unsigned_lit_small; lia).
assert (HS : st_ok_pi (fx := l_fx cx) segs VAL E0 lh_ss
  (restrict (w_H W') (@YK11.mkst (l_fx cx) regs' (Z_to_bv 64 (BASE + LO_HEAD)) mem' (YK11.seg_rom segs)))).
{ rewrite restrict_mkst_fx. unfold lh_ss.
  apply (@pa_entry_st_ok_full (l_fx cx) rc transportb_listing PI_transportb).
  - apply regs_ok_Eimg_Ereg.
  - vm_compute. reflexivity.
  - repeat apply Forall_cons; try apply Forall_nil; unfold lh_rg, lh_rg_sp, YP09.region_ok;
      cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
    + rewrite U25. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
      apply Forall_cons; [|apply Forall_nil].
      apply (lh_chunk1 _ _ 32 (p + off) 0 (p + off) b); [exact X32 | lia | lia | exact Vb].
    + rewrite U33. split; [unfold SHADOW_OFF in *; lia|]. split; [unfold SHADOW_OFF in *; lia|].
      split; [intros o Ho; lia|].
      apply Forall_cons; [|apply Forall_nil].
      apply (lh_chunk1 _ _ 34 sha 0 sha sb); [exact X34 | lia | lia | exact VS].
  - apply pairwise_disjoint_of_extents.
    unfold lh_rg, lh_rg_sp, extent_of_region. cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val].
    rewrite U25, U33. cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
    unfold kLowShadowBeg, kHighMemBeg, SHADOW_OFF in *.
    repeat split; first [exact I | lia].
  - unfold facts_ok, lh_G. cbn [f_atoms f_conds f_alias atoms_ok conds_ok alias_ok].
    unfold afact_ok, lh_PTRHI. cbn [af_lo af_hi af_al2].
    rewrite U26, U25, U32, U33, U34. rewrite !Z.pow_0_r, !Z.mod_1_r.
    repeat match goal with |- _ /\ _ => split end; try exact I; try (unfold SHADOW_OFF in *; lia).
    rewrite (can_denot_shadow _ 25 26 (p + off) SHADOW_OFF X25 X26 ltac:(lia) ltac:(unfold SHADOW_OFF; lia)
      ltac:(unfold SHADOW_OFF; lia)).
    cbn [sv_denot]. rewrite U33, Z.add_0_r. reflexivity. }
assert (HSH : sh_ok segs lh_Bx lh_SH E0 (mrestrict (w_H W') mem')) by constructor.
assert (HEI : img_env VAL A_LIM E0) by apply Eimg_env.
pose proof (env_agree_refl 512 E0) as HAG.
(* the op code: the byte mod 9 *)
assert (Hopc : lc_opc D c = b mod 9).
{ unfold lc_opc, TOP.fuzz_u8_m.
  replace (TOP.fi_n c =? 0) with false by (symmetry; apply Z.eqb_neq; exact Hn0).
  cbn [snd]. unfold DSpec.at8, DSpec.bz, b. f_equal.
  rewrite (nth_indep _ 0 (bv_unsigned (DSpec.b8 0)) Hj). rewrite map_nth. reflexivity. }
(* K1: the table reads as the image *)
assert (HRO : trans_rom_view_rd W' mem') by exact (K1 HP cx ly' S' W' regs' mem' md' e HB HC).
(* the arm's cut from the head's facts, at the registers the run leaves *)
assert (FIN : forall o regs2 X,
  (forall r, In r lh_kp -> YK11.getr regs2 r = YK11.getr regs' r) ->
  YK11.getr regs2 22 = w64 1 ->
  YK11.getr regs2 (Z_to_bv 5 24) = w64 (p + off + 1) ->
  YK11.getr regs2 (Z_to_bv 5 27) = w64 (nr - 1) ->
  b mod 9 = o ->
  @lc_st_arm rc B MT cx op o W' (lc_cfg cx (lo_arm o) regs2 mem' (with_vm_backing (m_vm_lazy md') X md'))).
{ intros o regs2 X KR Q22 Q24 Q27 Ho.
  exact (lh_close cx op ly' S' W' regs' mem' md' e regs2 X o LAWS HL Htw (conj R25 R23) R20 KR Q22 Q24 Q27 Hn0
           (eq_trans (eq_sym Ho) (eq_sym Hopc))). }
unfold lc_cfg.
lazymatch goal with |- SRr _ ?Wx _ ?Q =>
  change (SRr segs Wx (mkCfg (@YK11.mkst (l_fx cx) regs' (Z_to_bv 64 (BASE + LO_HEAD)) mem' (YK11.seg_rom segs)) md') Q)
end.
set (fx := l_fx cx) in *.
(* s6 = 1 as a literal, so the engine decides the UBSan cursor test `bltu s6, s8` *)
lh_pin_reg (22%bv : bv 5) (SLit 1) R22.
(* +0x58c .. +0x5a4: s8 = s9 + 1, the UBSan cursor test (taken), the shadow byte of s9, up to `beqz a0` *)
lh_step lh_SH 0x90c.
lh_branch lh_SH.
- (* the shadow byte is 0: the fast path to `bltu a1, a0` *)
  clear Hc.
  lh_step lh_SH 0x90c.
  lh_dispatch b X32 Rb FIN regs' [w64 b; w64 sha; w64 sb] X25 X23 W' mem' HRO.
- (* the shadow byte is in (0, 8): the slow path +0x16b8 .. +0x16c0 *)
  lazymatch goal with HAG1 : env_agree 512 _ _ |- _ =>
    pose proof (lh_beqz _ 34 sb false (eq_trans (proj1 HAG1 34%nat ltac:(lia)) X34) ltac:(lia) Hc) as Hs0 end.
  apply Z.eqb_neq in Hs0. clear Hc.
  assert (Hsb1 : (p + off) mod 8 < sb < 8) by (destruct Hsok as [Hs | Hs]; [exfalso; exact (Hs0 Hs) | exact Hs]).
  lh_step lh_SH 0x90c.
  lh_branch lh_SH.
  + (* `bge a1, a0` taken: refuted, the report call +0x1c60 is not reached *)
    exfalso.
    lazymatch goal with HAG1 : env_agree 512 _ _ |- _ =>
      pose proof (lh_bge _ (p + off) sb true (eq_trans (proj1 HAG1 25%nat ltac:(lia)) X25)
        (eq_trans (proj1 HAG1 34%nat ltac:(lia)) X34) ltac:(lia) Hsb1 Hc) as Hf end.
    discriminate Hf.
  + clear Hc.
    lh_step lh_SH 0x90c.
    lh_dispatch b X32 Rb FIN regs' [w64 b; w64 sha; w64 sb] X25 X23 W' mem' HRO.
Qed.

End head.

Print Assumptions lc_head_ok.
