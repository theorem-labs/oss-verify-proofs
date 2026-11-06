(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: the ASan+UBSan walk of lv2_refusals_forget (plugin-hostd/fuzz_command, image
   fuzz_command.asan-ubsan, entry BASE + AF_lv2_refusals_forget = 0x8cd54, 24 instructions, 96 bytes): it proves
   a Theorem Labs lane's `tlv2_refusals_forget_spec` (lib/B/Prog/lv2_refusals_forget_c.v) in the form of cgif_file_fuzzer's
   per-function walks: afn_pre at the entry, the symbolic executor over the position-abstract listing between the
   calls, the callee contracts record_c, arg_s_c and mix_call_c through cl_callS_wide, the return through paj_ret_at,
   and apost_base at the end. It is the B re-walk of the A walk lib/A/Prog/lv2_refusals_forget.v (+ _s1.v, _s2.v,
   a working branch cbd8900ed8c), where A inlines record() and xstrdup and B calls record and
   arg_s; the B code template was read from the Generation-N walk lib/B/Prog/lv2_refusals_forget.v (template only,
   not ported: a working branch 543f2c3645b).

   B's code (capstone on fuzz_command.asan-ubsan, sha256 658cefbe..., symbol lv2_refusals_forget):
     0x8cd54 addi sp,sp,-32; sd ra,24(sp); sd s0,16(sp); sd s1,8(sp); mv s1,a0; li a0,25
     0x8cd6c jal record (0x8a728)
     0x8cd70 mv s0,a0; bnez s1,0x8cd80; auipc a0 (A_HI 206); addi s1,a0,0x268 (= 0x21fe0, "*", A_OBJ 89)
     0x8cd80 mv a0,s0; mv a1,s1
     0x8cd88 jal arg_s (0x8a820)
     0x8cd8c auipc s1 (A_HI 207 = 0x5e3d8c); ld a0,-0x71c(s1) (A_OBJ 86 = 0x5e3670, g_rec.state); mv a1,s0
     0x8cd98 jal mix_call (0x8ad54)
     0x8cd9c sd a0,-0x71c(s1) (a plain word through s1 = A_HI 207: g_rec.state := mix_call's result)
     0x8cda0 ld ra,24(sp); ld s0,16(sp); ld s1,8(sp); addi sp,sp,32; ret
   There is no __asan_report_* call and no UBSan trap (unimp / ebreak) in the function, so it has no report edge to
   refute: the ASan checks and the UBSan traps are in record, arg_s and mix_call, whose contracts this walk takes.
   The only branch, `bnez s1` at 0x8cd74 (uri NULL or not), is split by paj_branch and both arms are joined at the
   call of arg_s in the state lrfb_ssC (lrfb_canon_ok), where s1 = a1 = the atom of the recorded string.

   Section hypotheses beyond the statement's: HB (the allocator record) and MTL (the meter's laws), as the A walk names
   them (lib/A/Prog/lv2_refusals_forget.v:58-60); and the per-binary facts a Theorem Labs lane proves only at the pinned image
   (PI := PB_cmd), each under a Theorem Labs lane's lemma name with its statement at this walk's abstract PAImg:
   `cmd_sig_prog_PB : cmd_sig_prog` (the program functions' call targets), `cmd_val_his_PB : cmd_val_his` (the auipc
   value A_HI 207 of the store at 0x8cd9c, a Theorem Labs lane 08:12Z), `cmd_img_facts_tfib` (lib/B/Prog/CmdRecImg.v), and
   `PRW : prog_rw SEGS B` (the hypothesis of lib/B/Prog/CmdRecCells.v PROG_WRITABLE). Every other per-binary fact is
   a Theorem Labs lane's lemma over them, by exact: CmdRecRo.v CMD_RO_IN, cmd_ro_ok_of_aro, RELRO_IMG, ROB; CmdRecRest.v
   cmd_ro_prog_apart, cmd_prog_img; CmdRecImg.v cmd_heap_tail_vis; CmdRecCells.v PROG_WRITABLE. *)
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require YZ00.
From Stdlib Require Import String ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require YO0f.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP0i YCbn.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YN3v YI04 YI00 YG0s.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq YG0q.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YI16 YM05 YC5d.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Rt Require Import RtDefs RtString.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require Import RecFacts RecModel RecInv.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import PaTable PaSym PaStep PaRun PaShadow PaJournal.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import CmdSyms CmdAddr CmdList CmdPa CmdPaLib.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import PaCall PaCallRun PaLibF PaLibG PaLibH PaSB PaDenot PaNoChain.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B Require Import YF0m.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import CmdGlob CmdBase CmdChk CmdRep CmdObj CmdRo CmdZsh PaArt.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import
xmalloc_c rec_calls_free_c record_c arg_s_c mix_call_c lv2_refusals_forget_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import
CmdRecBase CmdRecImg CmdRecCells CmdRecRo CmdRecRest.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import RecBLemmas.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require CmdRecAns.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.

(* ---- the atoms and the stops of the walk on B's listing (lib/B/Prog/CmdList.v, CmdAddr.v) ------------------ *)
(* the extra atoms above the 32 registers: g_rec.state at the entry (r_state R), and the string handed to arg_s *)
Definition L_H : nat := 32.
Definition L_S : nat := 33.
Definition lrfb_extra (h s : Z) : list word := map (Z_to_bv 64) [h; s].
(* the image's objects (cmd_objs index i is the atom A_OBJ i) and the auipc value of the store *)
Definition L_GREC : nat := A_OBJ 44.   (* 0x5e32c0, g_rec *)
Definition L_SPILL : nat := A_OBJ 53.  (* 0x5e3760, record.spill *)
Definition L_STATE : nat := A_OBJ 86.  (* 0x5e3670, g_rec.state = g_rec + 944: the ld at 0x8cd90 (PLdHi 207) *)
Definition L_STAR : nat := A_OBJ 89.   (* 0x21fe0, "*": the addi at 0x8cd7c (PAddHi 206) *)
Definition L_HSTATE : nat := A_HI 207. (* 0x5e3d8c, auipc s1 at 0x8cd8c; the sd at 0x8cd9c is a plain word through it *)
(* the listing offsets of the walk's stops (BASE + AF_lv2_refusals_forget = 0x8cd54) *)
Definition L_REC_RET : Z := AF_lv2_refusals_forget + 0x1c.   (* 0x8cd70, after record *)
Definition L_ARG_CALL : Z := AF_lv2_refusals_forget + 0x34.  (* 0x8cd88, jal arg_s: the arms of `bnez s1` meet *)
(* the footprint the statement gives (lv2_refusals_forget_c.v, apost_base's region list) *)
Definition lrfb_FP (O : list (Z * Z)) : list (Z * Z) :=
(A_G_REC, A_G_REC + REC_SIZE) :: (A_REC_SPILL, A_REC_SPILL + SC_SIZE) :: ablocks_fp O.
(* the effective argument and its address: uri, or the literal "*" (0x21fe0) when uri is NULL *)
Definition lrfb_x (uri : option (list byte)) : list byte := darg uri (bstr "*"%string).
Definition lrfb_s (pu : Z) : Z := if pu =? 0 then 0x21fe0 else pu.

(* ---- the symbolic states ----------------------------------------------------------------------------------- *)
(* the entry: the prologue's 32-byte frame below sp; the function has no shadow check of its own *)
Definition lrfb_facts0 : facts := mkFacts [(2%nat, mkAF (2 ^ 46) (2 ^ 47) 4)] [] [].
Definition lrfb_ss0 : sstate := mkSS AF_lv2_refusals_forget sr_atoms [stack_region 32] None lrfb_facts0.
(* the run to the call of record, the state after it (the frame kept, the clobbered registers at atoms 48..63),
   and the run to the branch at 0x8cd74 *)
Definition lrfb_runR := Eval vm_compute in sym_runN_pi cmd_tpi FUEL lrfb_ss0.
Definition lrfb_ss1 : sstate := Eval vm_compute in
  ss_after_call (fst lrfb_runR) (pick (ss_mem (fst lrfb_runR)) [0%nat]) 48 L_REC_RET.
Definition lrfb_runB := Eval vm_compute in sym_runN_pi cmd_tpi FUEL lrfb_ss1.
(* the join at the call of arg_s: s1 and a1 hold the atom L_S of the string (uri, or "*"), the facts are the atoms' *)
Definition lrfb_canon (ss : sstate) : sstate :=
  mkSS (ss_pc ss) (sr_set (sr_set (ss_regs ss) 9 (SOff L_S 0)) 11 (SOff L_S 0)) (ss_mem ss) None
    (mkFacts (f_atoms (ss_facts ss)) [] []).
Definition lrfb_ssC : sstate := Eval vm_compute in
  lrfb_canon (fst (sym_run_toN_pi cmd_tpi FUEL L_ARG_CALL
    (add_cond (fst lrfb_runB) (mkAC BC_NE (SOff 10 0) (SLit 0))))).
Lemma lrfb_ssC_facts : ss_facts lrfb_ssC = mkFacts (f_atoms (ss_facts lrfb_ssC)) [] [].
Proof. vm_compute. reflexivity. Qed.
(* the region of g_rec.state for the load at 0x8cd90 (seated after arg_s returns), and the region of the store at
   0x8cd9c (seated after mix_call returns), based at the auipc atom A_HI 207 *)
Definition lrfb_state_region : YP09.region := obj8_region 86 (SOff L_H 0).
Definition lrfb_store_region : YP09.region :=
  YP09.mkRegion (Some L_HSTATE) (-0x71c) (-0x714) (-0x71c) (-0x714) [].

(* ---- the recorder's representation over readers that agree (RecBLemmas' rd_agree and *_agree_in) ---------- *)
(* g_rec.state replaced, every other field and every block of the layout kept *)
Lemma lrfb_arep_set_state : forall bl rd rd' R Q h,
arep_at bl rd A_G_REC A_REC_SPILL R Q ->
rd_agree rd rd' A_G_REC OFF_STATE ->
rd_agree rd rd' (A_G_REC + OFF_HOST) 8 ->
rd_agree rd rd' A_REC_SPILL SC_SIZE ->
(forall pn, In pn (lay_blocks Q) -> rd_agree rd rd' (fst pn) (snd pn)) ->
aval_mem rd' (A_G_REC + OFF_STATE) 8 h -> 0 <= h < 2 ^ 64 ->
arep_at bl rd' A_G_REC A_REC_SPILL (set_state R h) Q.
Proof.
intros bl rd rd' R Q h (Hg8 & Hs8 & Hap & HC & HA & HR & HSC & HOWN) Hgl Hgh Hsp Hbl Hst Hh.
unfold arep_at. split; [exact Hg8|]. split; [exact Hs8|]. split; [exact Hap|].
split.
{ destruct HC as (Hlen & HlenQ & Hnc & Hcalls & Hspill & Hspf).
  unfold ag1_calls. cbn [r_calls r_spill set_state]. split; [exact Hlen|]. split; [exact HlenQ|].
  split; [apply (aval_mem_agree_in rd rd' A_G_REC OFF_STATE); [exact Hnc | exact Hgl | unfold OFF_NCALLS; lia | unfold OFF_NCALLS, OFF_STATE; cbn; lia]|].
  split.
  { intros i c P Hc HP. destruct (Hcalls i c P Hc HP) as [Hca Hf]. split; [|exact Hf].
    assert (Hi : (i < length (r_calls R))%nat) by (apply nth_error_Some; rewrite Hc; discriminate).
    apply (acall_at_agree bl bl rd rd'); [exact Hca | |].
    - apply (rd_agree_sub rd rd' A_G_REC OFF_STATE); [exact Hgl | unfold OFF_CALLS, CALL_SIZE; lia |].
      unfold OFF_CALLS, CALL_SIZE, OFF_STATE. lia.
    - intros pn Hpn. split; [exact (acall_at_in _ _ _ _ _ Hca pn Hpn)|]. apply Hbl.
      unfold lay_blocks. apply in_or_app. left. exact (In_concat_nth _ i P pn HP Hpn). }
  split; [|exact Hspf].
  apply (acall_at_agree bl bl rd rd'); [exact Hspill | unfold CALL_SIZE; exact Hsp |].
  intros pn Hpn. split; [exact (acall_at_in _ _ _ _ _ Hspill pn Hpn)|]. apply Hbl.
  unfold lay_blocks. apply in_or_app. right. apply in_or_app. left. exact Hpn. }
split.
{ cbn [r_answer set_state]. unfold aanswer_at in *.
  destruct (r_answer R) as [x|], (l_answer Q) as [pn|] eqn:EA; try contradiction.
  - destruct HA as (V & Hnz & Hin & Hlen & Hstr & Hlx).
    assert (Hpn : In pn (lay_blocks Q)).
    { unfold lay_blocks. rewrite EA. apply in_or_app. right. apply in_or_app. right. apply in_or_app. left. left. reflexivity. }
    split; [apply (aval_mem_agree_in rd rd' A_G_REC OFF_STATE); [exact V | exact Hgl | unfold OFF_ANSWER; lia | unfold OFF_ANSWER, OFF_STATE; cbn; lia]|].
    split; [exact Hnz|]. split; [exact Hin|]. split; [exact Hlen|]. split; [|exact Hlx].
    apply (astr_atR_agree_in rd rd' (fst pn) (snd pn)); [exact Hstr | exact (Hbl pn Hpn) | lia | lia].
  - apply (aval_mem_agree_in rd rd' A_G_REC OFF_STATE); [exact HA | exact Hgl | unfold OFF_ANSWER; lia | unfold OFF_ANSWER, OFF_STATE; cbn; lia]. }
split.
{ cbn [r_reply set_state]. unfold areply_at in *.
  destruct (r_reply R) as [x|], (l_reply Q) as [pn|] eqn:ER; try contradiction.
  - destruct HR as (A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8).
    assert (Hpn : In pn (lay_blocks Q)).
    { unfold lay_blocks. rewrite ER. apply in_or_app. right. apply in_or_app. right. apply in_or_app. right. left. reflexivity. }
    split; [apply (aval_mem_agree_in rd rd' A_G_REC OFF_STATE); [exact A1 | exact Hgl | unfold OFF_REPLY; lia | unfold OFF_REPLY, OFF_STATE; cbn; lia]|].
    split; [apply (aval_mem_agree_in rd rd' A_G_REC OFF_STATE); [exact A2 | exact Hgl | unfold OFF_REPLY_SIZE; lia | unfold OFF_REPLY_SIZE, OFF_STATE; cbn; lia]|].
    split; [exact A3|]. split; [exact A4|]. split; [exact A5|]. split; [exact A6|]. split; [|exact A8].
    apply (abytes_atR_agree_in rd rd' (fst pn) (snd pn)); [exact A7 | exact (Hbl pn Hpn) | lia | lia].
  - destruct HR as (A1 & A2).
    split; [apply (aval_mem_agree_in rd rd' A_G_REC OFF_STATE); [exact A1 | exact Hgl | unfold OFF_REPLY; lia | unfold OFF_REPLY, OFF_STATE; cbn; lia]|].
    apply (aval_mem_agree_in rd rd' A_G_REC OFF_STATE); [exact A2 | exact Hgl | unfold OFF_REPLY_SIZE; lia | unfold OFF_REPLY_SIZE, OFF_STATE; cbn; lia]. }
split.
{ destruct HSC as (Vr & Vc & Vn & Vs & Vh & Rr & Rc & Rn & Rs & Rh). unfold ag1_scalars.
  cbn [r_refuse r_code r_nreplies r_state r_host set_state].
  split; [apply (aval_mem_agree_in rd rd' A_G_REC OFF_STATE); [exact Vr | exact Hgl | unfold OFF_REFUSE; lia | unfold OFF_REFUSE, OFF_STATE; cbn; lia]|].
  split; [apply (aval_mem_agree_in rd rd' A_G_REC OFF_STATE); [exact Vc | exact Hgl | unfold OFF_CODE; lia | unfold OFF_CODE, OFF_STATE; cbn; lia]|].
  split; [apply (aval_mem_agree_in rd rd' A_G_REC OFF_STATE); [exact Vn | exact Hgl | unfold OFF_NREPLIES; lia | unfold OFF_NREPLIES, OFF_STATE; cbn; lia]|].
  split; [exact Hst|].
  split; [apply (aval_mem_agree_in rd rd' (A_G_REC + OFF_HOST) 8); [exact Vh | exact Hgh | lia | cbn; lia]|].
  repeat split; lia. }
exact HOWN.
Qed.

(* ---- record()'s slot ------------------------------------------------------------------------------------- *)
Lemma lrfb_state_record : forall R fn A, r_state (rec_record R fn A) = r_state R.
Proof. intros R fn A. unfold rec_record. destruct (Nat.ltb (length (r_calls R)) 16); reflexivity. Qed.
Lemma lrfb_m_eq : forall R uri, lv2_refusals_forget_m R uri =
  set_state (rec_record R REC_LV2_REFUSALS_FORGET [lrfb_x uri]) (mixcall (r_state R) REC_LV2_REFUSALS_FORGET [lrfb_x uri]).
Proof. intros R uri. unfold lv2_refusals_forget_m, rec_stub_mix, rec_mix. cbn [fst snd]. rewrite lrfb_state_record. reflexivity. Qed.
Lemma lrfb_slot_cases : forall R,
(exists i, 0 <= i < REC_CALLS_MAX /\ rec_slot R = A_G_REC + OFF_CALLS + CALL_SIZE * i) \/ rec_slot R = A_REC_SPILL.
Proof.
intros R. unfold rec_slot. destruct (Nat.ltb_spec (length (r_calls R)) 16) as [Hlt | Hge]; [left | right; reflexivity].
exists (Z.of_nat (length (r_calls R))). split; [unfold REC_CALLS_MAX; lia | reflexivity].
Qed.
Lemma lrfb_slot_in : forall R a, rec_slot R <= a < rec_slot R + CALL_SIZE ->
(A_G_REC + OFF_CALLS <= a < A_G_REC + OFF_ANSWER) \/ (A_REC_SPILL <= a < A_REC_SPILL + SC_SIZE).
Proof.
intros R a. unfold rec_slot. destruct (Nat.ltb_spec (length (r_calls R)) 16) as [Hlt | Hge]; intros Ha; [left | right];
unfold A_G_REC, OFF_CALLS, OFF_ANSWER, CALL_SIZE, A_REC_SPILL, SC_SIZE in *; lia.
Qed.

Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
(* cgif's region_kept over aview for a region whose window bytes stay present (socket_send's B walk,
   ss_region_kept_hi2): the call's world may grow *)
Lemma lrfb_region_kept_hi2 : forall (segs : list Segment) E H H2 (m m2 : word -> option byte) n b lo hi wlo whi cs,
bv_unsigned (ew E n) = b ->
(forall a, b + lo <= a < b + hi -> aview segs H2 m2 a = aview segs H m a) ->
(forall a, b + wlo <= a < b + whi -> apresent H2 m2 a) ->
region_kept segs E (mrestrict H m) (mrestrict H2 m2) (YP09.mkRegion (Some n) lo hi wlo whi cs).
Proof.
intros segs E H H2 m m2 n b lo hi wlo whi cs Hn Hav Hp.
split; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi base_val]; rewrite Hn; intros a Ha.
- apply (mbyte_of_aview segs). apply Hav. exact Ha.
- intros _. apply (apresent_writable segs). apply Hp. exact Ha.
Qed.
Section f.
Context {PI : PAImg cmd_listing}.
#[local] Notation SEGS := (@pa_segs _ cmd_listing PI).
#[local] Notation VAL := (@pa_val _ cmd_listing PI).
#[local] Notation BASE := (@pa_val _ cmd_listing PI A_TEXT).
#[local] Notation SIG s := (@pa_sigma _ cmd_listing PI s).
#[local] Notation rdW W mem := (aview SEGS (w_H W) mem).
(* a symbolic state with other register forms of the same values and fewer facts (the A walk's lrf_st_ok_canon) *)
Lemma lrfb_st_ok_canon : forall E ss ms sr G,
st_ok_pi SEGS VAL E ss ms -> (forall r, sv_denot E (sr_get sr r) = sv_denot E (sr_get (ss_regs ss) r)) -> facts_ok E G ->
st_ok_pi SEGS VAL E (mkSS (ss_pc ss) sr (ss_mem ss) (ss_resv ss) G) ms.
Proof.
intros E [pc sr0 fr0 m0 rv0 G0] ms sr G (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9) Hr HG.
unfold abs_ss, setpc in *. cbn [ss_pc ss_regs ss_fregs ss_mem ss_resv ss_facts] in *.
split; [exact H1|]. split; [exact H2|]. split; [exact H3|]. split; [exact H4|]. split; [exact H5|]. split; [exact H6|].
split; [|split; [exact H8 | exact HG]].
intros r. rewrite (H7 r). symmetry. apply Hr.
Qed.
Lemma lrfb_facts_atoms : forall E at0 cs al, facts_ok E (mkFacts at0 cs al) -> facts_ok E (mkFacts at0 [] []).
Proof. intros E at0 cs al [Ha _]. split; [exact Ha | split; exact I]. Qed.
(* both arms of `bnez s1` reach the call of arg_s in the state lrfb_ssC, whose s1 and a1 are the atom of the string
   (the A walk's lrf_canon2) *)
Lemma lrfb_canon_ok : forall E ss ms v,
st_ok_pi SEGS VAL E ss ms ->
ss_pc ss = ss_pc lrfb_ssC -> ss_mem ss = ss_mem lrfb_ssC -> ss_resv ss = None ->
f_atoms (ss_facts ss) = f_atoms (ss_facts lrfb_ssC) ->
forallb (fun r => sv_eqb (sr_get (ss_regs ss) r) (sr_get (ss_regs lrfb_ssC) r) ||
   (sv_eqb (sr_get (ss_regs ss) r) v && sv_eqb (sr_get (ss_regs lrfb_ssC) r) (SOff L_S 0))) all_regs = true ->
sv_denot E v = sv_denot E (SOff L_S 0) ->
st_ok_pi SEGS VAL E lrfb_ssC ms.
Proof.
intros E [pc sr0 fr0 m0 rv0 G0] ms v HS Hpc Hm Hrv Hat Hb Hv.
cbn [ss_pc ss_mem ss_resv ss_facts ss_regs] in Hpc, Hm, Hrv, Hat, Hb.
pose proof HS as (_ & _ & _ & _ & _ & _ & _ & _ & H9). unfold abs_ss, setpc in H9. cbn [ss_facts] in H9.
assert (HG : facts_ok E (ss_facts lrfb_ssC)).
{ rewrite lrfb_ssC_facts. destruct G0 as [at0 cs al]. cbn [f_atoms] in Hat. subst at0. exact (lrfb_facts_atoms E _ cs al H9). }
assert (Hr : forall r, sv_denot E (sr_get (ss_regs lrfb_ssC) r) = sv_denot E (sr_get sr0 r)).
{ intros r. pose proof (all_regs_in r) as Hin.
  pose proof (proj1 (forallb_forall _ _) Hb r Hin) as Hbr. cbv beta in Hbr.
  apply orb_true_iff in Hbr as [H1 | H2].
  - rewrite (sv_eqb_eq _ _ H1). reflexivity.
  - apply andb_prop in H2 as [H2 H3]. rewrite (sv_eqb_eq _ _ H2), (sv_eqb_eq _ _ H3). symmetry. exact Hv. }
pose proof (lrfb_st_ok_canon E _ ms (ss_regs lrfb_ssC) (ss_facts lrfb_ssC) HS Hr HG) as H.
cbn [ss_pc ss_mem ss_resv] in H. rewrite Hpc, Hm, Hrv in H.
exact H.
Qed.
Lemma lrfb_U_atom : forall E m v, ew E m = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 -> U E (SOff m 0) = v.
Proof.
intros E m v Hm Hv. unfold U. cbn [sv_denot]. rewrite Hm, Z.add_0_r, Z_to_bv_bv_unsigned.
apply unsigned_lit_small. exact Hv.
Qed.
Section e.
Variable B : asyms.
Variable MT : ameter_ops.
#[local] Notation RLO := CMD_RLO.
#[local] Notation RHI := CMD_RHI.
(* the statement's Section hypotheses (lv2_refusals_forget_c.v, Section e) *)
Hypothesis TRECORD : forall fx0 : YK11.FPState, @trecord_spec fx0 rc SK PI B MT.
Hypothesis TARG_S : forall fx0 : YK11.FPState, @targ_s_spec fx0 rc SK PI B MT.
Hypothesis TMIX_CALL : forall fx0 : YK11.FPState, @tmix_call_spec fx0 rc SK PI B MT.
Hypothesis VOBJS : cmd_val_objs.
(* the walk's hypotheses, with the A walk's names (lib/A/Prog/lv2_refusals_forget.v:58-60): HB, the allocator record
   (lib/B/YF0m.v, Record CmdBSyms); MTL, the meter's laws *)
Hypothesis HB : CmdBSyms B.
Hypothesis MTL : ameter_laws MT.
(* the call target of every program function (lib/B/Prog/CmdObj.v cmd_sig_prog; a Theorem Labs lane's CmdRecRest.v cmd_sig_prog_PB
   at the pinned image) *)
Hypothesis cmd_sig_prog_PB : cmd_sig_prog.
(* the auipc values (lib/B/Prog/CmdObj.v cmd_val_his; a Theorem Labs lane's CmdRecRest.v cmd_val_his_PB at the pinned image):
   A_HI 207 = 0x5e3d8c is the base of the plain-word store `sd a0,-0x71c(s1)` at 0x8cd9c (a Theorem Labs lane 08:12Z) *)
Hypothesis cmd_val_his_PB : cmd_val_his.
(* the per-binary image facts (a Theorem Labs lane's lib/B/Prog/CmdRecBase.v cmd_img_facts): a Theorem Labs lane proves them at the pinned image
   (CmdRecImg.v cmd_img_facts_tfib, at tfibsegs); this walk is over an abstract PAImg, so it takes that lemma's
   statement at its own segments, under the lemma's name *)
Hypothesis cmd_img_facts_tfib : forall B0, CmdBSyms B0 -> @cmd_img_facts SK SEGS B0.
(* the program's statics are writable at every state (the core's prog_rw, the hypothesis of a Theorem Labs lane's
   CmdRecCells.v PROG_WRITABLE) *)
Hypothesis PRW : prog_rw SEGS B.
Let LAWS : AR_laws SEGS B := AR_laws_ok SEGS B.
Let IMG : @cmd_img_facts SK SEGS B := cmd_img_facts_tfib B HB.
Let CMD_RO_IN : cmd_ro_in (in_roP SEGS RLO RHI) := CmdRecRo.CMD_RO_IN (SK := SK) SEGS B LAWS HB IMG.
Let cmd_prog_img : forall a, Exists (in_zr a) TFIB_PROG_STATIC -> in_img SEGS a :=
  CmdRecRest.cmd_prog_img (SK := SK) SEGS B LAWS HB IMG.
Let cmd_ro_prog_apart : forall a, in_roP SEGS RLO RHI a -> in_img SEGS a /\ ~ Exists (in_zr a) TFIB_PROG_STATIC :=
  CmdRecRest.cmd_ro_prog_apart (SK := SK) SEGS B LAWS HB IMG.
Let cmd_ro_ok_of_aro : forall ly S (W : world SEGS) mem md, AR SEGS B ly S W mem md ->
  arodata_okP SEGS RLO RHI B (rdW W mem) -> cmd_ro_ok (rdW W mem) :=
  CmdRecRo.cmd_ro_ok_of_aro (SK := SK) SEGS B LAWS HB IMG.
Let RELRO_IMG : forall a, RLO <= a < RHI -> in_img SEGS a := CmdRecRo.RELRO_IMG (SK := SK) SEGS B LAWS HB IMG.
Let ROB : ro_below_ofl SEGS RLO RHI := CmdRecRo.ROB (SK := SK) SEGS B LAWS HB IMG.
Let cmd_heap_tail_vis : forall ly S (W : world SEGS) mem md p n e, AR SEGS B ly S W mem md ->
  In (p, n) (ablocks B ly S) -> p <= e < p + req_size n -> atail_vis SEGS W mem e :=
  CmdRecImg.cmd_heap_tail_vis SEGS B LAWS HB.
Let PROG_WRITABLE : forall (m : word -> option byte) a, inFP cmd_PG a -> writable_at SEGS m a :=
  CmdRecCells.PROG_WRITABLE SEGS B LAWS HB PRW.
Let RUNP := SRr_run_pi_AJ (L := cmd_listing) (PL := PL_cmd) (PI := PI) B LAWS.
Let RUNC := SRr_run_pi_AJ_call (L := cmd_listing) (PL := PL_cmd) (PI := PI) B LAWS.
Let RUNTOP := SRr_run_to_pi_AJ (L := cmd_listing) (PL := PL_cmd) (PI := PI) B LAWS.
Let BR := paj_branch (PI := PI).
Let RET := paj_ret_at (PL := PL_cmd) (PI := PI).

(* ---- the atoms' values and the call targets -------------------------------------------------------------- *)
Lemma lrfb_grec_val : VAL L_GREC = A_G_REC.
Proof. unfold L_GREC. rewrite (VOBJS 44%nat ltac:(vm_compute; lia)). vm_compute. reflexivity. Qed.
Lemma lrfb_state_val : VAL (A_OBJ 86) = A_G_REC + OFF_STATE.
Proof. rewrite (VOBJS 86%nat ltac:(vm_compute; lia)). vm_compute. reflexivity. Qed.
Lemma lrfb_star_val : VAL (A_OBJ 89) = 0x21fe0.
Proof. rewrite (VOBJS 89%nat ltac:(vm_compute; lia)). vm_compute. reflexivity. Qed.
Lemma lrfb_hstate_val : VAL L_HSTATE = 0x5e3d8c.
Proof. unfold L_HSTATE. rewrite (cmd_val_his_PB 207%nat ltac:(vm_compute; lia)). vm_compute. reflexivity. Qed.
Lemma lrfb_sig_arg_s : SIG CS_arg_s = BASE + AF_arg_s.
Proof. rewrite (cmd_sig_prog_PB CS_arg_s ltac:(vm_compute; repeat (first [left; reflexivity | right]))). reflexivity. Qed.
Lemma lrfb_sig_mix_call : SIG CS_mix_call = BASE + AF_mix_call.
Proof. rewrite (cmd_sig_prog_PB CS_mix_call ltac:(vm_compute; repeat (first [left; reflexivity | right]))). reflexivity. Qed.

(* ---- the footprint -------------------------------------------------------------------------------------- *)
Lemma lrfb_in_PG_grec : forall a, A_G_REC <= a < A_G_REC + REC_SIZE -> Exists (in_zr a) TFIB_PROG_STATIC.
Proof. intros a Ha. apply Exists_cons_hd. unfold in_zr. cbn [fst snd]. exact Ha. Qed.
Lemma lrfb_in_PG_spill : forall a, A_REC_SPILL <= a < A_REC_SPILL + SC_SIZE -> Exists (in_zr a) TFIB_PROG_STATIC.
Proof. intros a Ha. apply Exists_cons_tl. apply Exists_cons_hd. unfold in_zr. cbn [fst snd]. exact Ha. Qed.

Lemma lrfb_inFP_grec : forall O a, A_G_REC <= a < A_G_REC + REC_SIZE -> inFP (lrfb_FP O) a.
Proof. intros O a Ha. exists (A_G_REC, A_G_REC + REC_SIZE). split; [left; reflexivity | cbn [fst snd]; exact Ha]. Qed.
Lemma lrfb_inFP_spill : forall O a, A_REC_SPILL <= a < A_REC_SPILL + SC_SIZE -> inFP (lrfb_FP O) a.
Proof.
intros O a Ha. exists (A_REC_SPILL, A_REC_SPILL + SC_SIZE). split; [right; left; reflexivity | cbn [fst snd]; exact Ha].
Qed.
(* a write of the walk to g_rec: the footprint names it, and it is a program static of the image *)
Lemma lrfb_awr_PG : forall STK sp0 O bl0 blc fr0 ly own a,
inFP (lrfb_FP O) a -> Exists (in_zr a) TFIB_PROG_STATIC ->
awr_byte SEGS B STK sp0 (lrfb_FP O) bl0 blc fr0 ly own a.
Proof.
intros STK sp0 O bl0 blc fr0 ly own a Hfp HPG. right; right; right; right. left.
split; [exact Hfp|]. split; [rewrite (ts_prog B HB); exact HPG | exact (cmd_prog_img a HPG)].
Qed.
Lemma lrfb_awr_cons_grec : forall E r rs STK sp0 O bl0 blc fr0 ly own,
YP09.r_base r = Some L_GREC -> img_env VAL A_LIM E ->
0 <= YP09.r_wlo r -> YP09.r_whi r <= REC_SIZE ->
awr_ok SEGS B E rs STK sp0 (lrfb_FP O) bl0 blc fr0 ly own -> awr_ok SEGS B E (r :: rs) STK sp0 (lrfb_FP O) bl0 blc fr0 ly own.
Proof.
intros E r rs STK sp0 O bl0 blc fr0 ly own Hb HEI Hlo Hhi H.
eapply awr_ok_cons_gen with (n := L_GREC) (b := A_G_REC); [exact Hb | | | exact H].
- rewrite (HEI L_GREC ltac:(unfold L_GREC, A_OBJ, A_TEXT, A_LIM; lia)). exact lrfb_grec_val.
- intros a Ha. assert (Ha' : A_G_REC <= a < A_G_REC + REC_SIZE) by lia.
  exact (lrfb_awr_PG STK sp0 O bl0 blc fr0 ly own a (lrfb_inFP_grec O a Ha') (lrfb_in_PG_grec a Ha')).
Qed.
(* the region of the store at 0x8cd9c: based at the auipc atom A_HI 207, the 8 bytes of g_rec.state *)
Lemma lrfb_awr_cons_hstate : forall E r rs STK sp0 O bl0 blc fr0 ly own,
YP09.r_base r = Some L_HSTATE -> img_env VAL A_LIM E ->
-0x71c <= YP09.r_wlo r -> YP09.r_whi r <= -0x71c + 8 ->
awr_ok SEGS B E rs STK sp0 (lrfb_FP O) bl0 blc fr0 ly own -> awr_ok SEGS B E (r :: rs) STK sp0 (lrfb_FP O) bl0 blc fr0 ly own.
Proof.
intros E r rs STK sp0 O bl0 blc fr0 ly own Hb HEI Hlo Hhi H.
eapply awr_ok_cons_gen with (n := L_HSTATE) (b := 0x5e3d8c); [exact Hb | | | exact H].
- rewrite (HEI L_HSTATE ltac:(unfold L_HSTATE, A_HI, A_TEXT, A_LIM; lia)). exact lrfb_hstate_val.
- intros a Ha. assert (Ha' : A_G_REC <= a < A_G_REC + REC_SIZE) by (unfold A_G_REC, REC_SIZE; lia).
  exact (lrfb_awr_PG STK sp0 O bl0 blc fr0 ly own a (lrfb_inFP_grec O a Ha') (lrfb_in_PG_grec a Ha')).
Qed.

(* ---- what a journal with the call's footprint keeps ------------------------------------------------------ *)
Lemma lrfb_heap_off_img : forall ly S (W : world SEGS) mem md p n a, AR SEGS B ly S W mem md ->
In (p, n) (ablocks B ly S) -> p <= a < p + req_size n -> ~ in_img SEGS a.
Proof.
intros ly S W mem md p n a HAR Hin Ha Hi. pose proof (blk_off_imgP B ly S W mem md p n HAR Hin) as Ho.
pose proof (pa_img_range a Hi) as Hr. unfold off_img in Ho. lia.
Qed.
Lemma lrfb_PG_img : forall a, Exists (in_zr a) TFIB_PROG_STATIC -> 0x10000 <= a < 0x606000.
Proof. intros a H. exact (pa_img_range a (cmd_prog_img a H)). Qed.
Lemma lrfb_inFP_inv : forall O a, inFP (lrfb_FP O) a ->
Exists (in_zr a) TFIB_PROG_STATIC \/ exists pn, In pn O /\ fst pn <= a < fst pn + req_size (snd pn).
Proof.
intros O a (r & Hr & Ha). destruct Hr as [<- | [<- | Hr]]; cbn [fst snd] in Ha.
- left. apply lrfb_in_PG_grec. exact Ha.
- left. apply lrfb_in_PG_spill. exact Ha.
- right. unfold ablocks_fp in Hr. apply in_map_iff in Hr as ([p n] & <- & Hin). exists (p, n). split; [exact Hin | exact Ha].
Qed.
Lemma lrfb_sink_closed : forall O ly S (W : world SEGS) mem md, AR SEGS B ly S W mem md ->
(forall pn, In pn O -> In pn (ablocks B ly S)) -> ~ YI16.sink_open_fp (lrfb_FP O).
Proof.
intros O ly S W mem md HAR HO. apply sink_closed_pos. unfold lrfb_FP.
constructor; [cbn; unfold A_G_REC; lia|]. constructor; [cbn; unfold A_REC_SPILL; lia|].
unfold ablocks_fp. apply Forall_map. apply Forall_forall. intros [p n] Hin. cbn [fst].
destruct (al_blocks _ _ LAWS _ _ _ _ _ p n HAR (HO _ Hin)) as (_ & H4096 & _). lia.
Qed.
(* a read-only byte outside the runtime's statics is kept by the journal of the call *)
Lemma lrfb_kept_ro : forall STK sp0 O ly S (W : world SEGS) mem md own ly' S' (W' : world SEGS) mem' md' k a,
ajournal SEGS B STK sp0 (lrfb_FP O) ly S W mem md own ly' S' W' mem' md' k -> AR SEGS B ly S W mem md ->
(forall pn, In pn O -> In pn (ablocks B ly S)) ->
in_roP SEGS RLO RHI a -> ~ Exists (in_zr a) (as_owned_static B) -> ~ (as_errno B <= a < as_errno B + 4) ->
rdW W' mem' a = rdW W mem a.
Proof.
intros STK sp0 O ly S W mem md own ly' S' W' mem' md' k a HJ HAR HO Hro Hown Herr.
pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HIMG & _).
destruct (cmd_ro_prog_apart a Hro) as [Himg HnPG].
apply HIMG; [exact Himg | exact Hown | exact Herr |].
split; [intros Hso; exfalso; exact (lrfb_sink_closed O ly S W mem md HAR HO Hso)|].
intros Hfp. destruct (lrfb_inFP_inv O a Hfp) as [HPG | ([p n] & Hin & Ha)]; [exact (HnPG HPG)|].
exact (lrfb_heap_off_img ly S W mem md p n a HAR (HO _ Hin) Ha Himg).
Qed.
(* a byte of a live block the recorder does not own is kept by the journal of the call *)
Lemma lrfb_kept_heap : forall STK sp0 O ly S (W : world SEGS) mem md own ly' S' (W' : world SEGS) mem' md' k q m i,
ajournal SEGS B STK sp0 (lrfb_FP O) ly S W mem md own ly' S' W' mem' md' k -> AR SEGS B ly S W mem md ->
(forall pn, In pn O -> In pn (ablocks B ly S)) ->
In (q, m) (ablocks B ly S) -> ~ In (q, m) O -> In (q, m) (ablocks B ly' S') -> 0 <= i < req_size m ->
rdW W' mem' (q + i) = rdW W mem (q + i).
Proof.
intros STK sp0 O ly S W mem md own ly' S' W' mem' md' k q m i HJ HAR HO Hin HnO Hin' Hi.
pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & HBLK & _).
apply (HBLK q m i Hin Hin' Hi). intros Hfp.
destruct (lrfb_inFP_inv O (q + i) Hfp) as [HPG | ([p n] & HinO & Ha)].
- exact (lrfb_heap_off_img ly S W mem md q m (q + i) HAR Hin ltac:(lia) (cmd_prog_img _ HPG)).
- assert (Hne : (q, m) <> (p, n)) by (intros E; apply HnO; rewrite E; exact HinO).
  pose proof (sep_blocks SEGS B LAWS ly S W mem md q m p n HAR Hin (HO _ HinO) Hne) as D.
  unfold zdisjoint in D. cbn [fst snd] in D, Ha. lia.
Qed.
(* arodata_okP survives a journal with the call's footprint (CmdBase.v arodata_ok_journalP) *)
Lemma lrfb_aro_kept : forall STK sp0 O ly S (W : world SEGS) mem md own ly' S' (W' : world SEGS) mem' md' k,
ajournal SEGS B STK sp0 (lrfb_FP O) ly S W mem md own ly' S' W' mem' md' k -> AR SEGS B ly S W mem md ->
(forall pn, In pn O -> In pn (ablocks B ly S)) ->
arodata_okP SEGS RLO RHI B (rdW W mem) -> arodata_okP SEGS RLO RHI B (rdW W' mem').
Proof.
intros STK sp0 O ly S W mem md own ly' S' W' mem' md' k HJ HAR HO HR.
apply (arodata_ok_journalP SEGS RLO RHI RELRO_IMG (RO := ROB) B STK sp0 (lrfb_FP O) ly S W mem md own ly' S' W' mem' md' k HJ);
[| exact HR].
intros a Hro Hfp. destruct (cmd_ro_prog_apart a Hro) as [Himg HnPG].
destruct (lrfb_inFP_inv O a Hfp) as [HPG | ([p n] & Hin & Ha)]; [exact (HnPG HPG)|].
exact (lrfb_heap_off_img ly S W mem md p n a HAR (HO _ Hin) Ha Himg).
Qed.

(* ---- the recorder's representation (lib/B/Prog/CmdRep.v) ------------------------------------------------ *)
Lemma lrfb_aval_mem_kept : forall (rd rd' : reader) a n v, aval_mem rd a n v ->
(forall k, (k < n)%nat -> rd' (a + Z.of_nat k) = rd (a + Z.of_nat k)) -> aval_mem rd' a n v.
Proof. intros rd rd' a n v H Hk k Hkn. rewrite (Hk k Hkn). exact (H k Hkn). Qed.
Lemma lrfb_rabytes_kept : forall (rd rd' : reader) a l, abytes_atR rd a l ->
(forall i, 0 <= i < Z.of_nat (length l) -> rd' (a + i) = rd (a + i)) -> abytes_atR rd' a l.
Proof. intros rd rd' a l H Hk i Hi. rewrite (Hk (Z.of_nat i) ltac:(lia)). exact (H i Hi). Qed.
Lemma lrfb_rastr_kept : forall (rd rd' : reader) a s, astr_atR rd a s ->
(forall i, 0 <= i < Z.of_nat (length s) + 1 -> rd' (a + i) = rd (a + i)) -> astr_atR rd' a s.
Proof.
intros rd rd' a s [H1 H2] Hk. split; [|exact H2]. apply (lrfb_rabytes_kept rd); [exact H1|].
intros i Hi. rewrite length_app in Hi. cbn [length] in Hi. apply Hk. lia.
Qed.
(* every block of O is a live block: O is the layout's blocks (RecBLemmas lay_blocks_in) *)
Lemma lrfb_rep_O_in : forall ly S rd R O, rec_repA B ly S rd R O -> forall pn, In pn O -> In pn (ablocks B ly S).
Proof.
intros ly S rd R O (Q & HA & HOQ) pn Hpn. exact (lay_blocks_in _ _ _ _ R Q HA pn (proj1 (HOQ pn) Hpn)).
Qed.
Lemma lrfb_bsum_perm : forall l1 l2, Permutation l1 l2 -> bsum l1 = bsum l2.
Proof.
intros l1 l2 H. induction H as [| x l1 l2 _ IH | x y l | l1 l2 l3 _ IH1 _ IH2]; cbn [bsum fold_right] in *;
unfold bsum in *; cbn [fold_right] in *; lia.
Qed.
Lemma lrfb_bsum_nonneg : forall ly S (W : world SEGS) mem md l, AR SEGS B ly S W mem md ->
(forall pn, In pn l -> In pn (ablocks B ly S)) -> 0 <= bsum l.
Proof.
intros ly S W mem md l HAR Hl. induction l as [|[p n] l IH]; cbn [bsum fold_right]; [lia|].
unfold bsum in IH. cbn [fold_right snd].
destruct (al_blocks _ _ LAWS _ _ _ _ _ p n HAR (Hl _ (or_introl eq_refl))) as (_ & _ & _ & _ & _ & _ & Hn).
assert (0 <= fold_right (fun b acc => snd b + acc) 0 l) by (apply IH; intros pn Hpn; apply Hl; right; exact Hpn). lia.
Qed.

(* ---- the argument --------------------------------------------------------------------------------------- *)
(* the literal "*" (0x21fe0) is no runtime-owned byte and not the errno cell (the record's tables, lib/B/YF0m.v) *)
Lemma lrfb_star_unowned : forall i, 0 <= i < 2 ->
in_roP SEGS RLO RHI (0x21fe0 + i) -> in_roP SEGS RLO RHI (0x21fe0 + i) /\ ~ Exists (in_zr (0x21fe0 + i)) (as_owned_static B) /\
~ (as_errno B <= 0x21fe0 + i < as_errno B + 4).
Proof.
intros i Hi Hro. split; [exact Hro|]. rewrite (ts_owned B HB), (ts_errno B HB). split; [|unfold TFIB_ERRNO; lia].
intros Hex. apply Exists_exists in Hex as (r & Hr & Ha). unfold in_zr in Ha.
assert (Hb : existsb (fun r => (fst r <=? 0x21fe0 + i) && (0x21fe0 + i <? fst r + snd r)) Tfib_owned_static = true).
{ apply existsb_exists. exists r. split; [exact Hr|]. apply andb_true_intro. split; [apply Z.leb_le | apply Z.ltb_lt]; lia. }
assert (E : i = 0 \/ i = 1) by lia. destruct E as [-> | ->]; vm_compute in Hb; discriminate Hb.
Qed.
(* the string argument's address: 0 for NULL, else a byte of a live block or of the image *)
Lemma lrfb_pu_cases : forall ly S (W : world SEGS) mem md O pu uri, AR SEGS B ly S W mem md ->
astr_argA B ly S (rdW W mem) (in_roP SEGS RLO RHI) O pu uri ->
(uri = None /\ pu = 0) \/ (uri <> None /\ 0 < pu < 2 ^ 64).
Proof.
intros ly S W mem md O pu uri HAR HSTR. destruct uri as [x|]; [right | left; split; [reflexivity | exact HSTR]].
split; [discriminate|].
destruct HSTR as (Hp0 & _ & _ & [((q & m & Hqm & Hq & Hqe) & _) | (HRO & _)]).
- destruct (al_blocks _ _ LAWS _ _ _ _ _ q m HAR Hqm) as (_ & Hq4 & Hqc & _ & _ & _ & Hm).
  pose proof (req_size_pos m ltac:(lia)) as [_ Hrm]. pose proof asan_consts as (C1 & _). lia.
- destruct (HRO 0 ltac:(lia)) as (Hro & _). rewrite Z.add_0_r in Hro.
  pose proof (pa_img_range pu (proj1 (cmd_ro_prog_apart pu Hro))). lia.
Qed.

(* ---- the program's statics and the callee's journal ----------------------------------------------------- *)
Lemma lrfb_PG_unowned : forall a, Exists (in_zr a) TFIB_PROG_STATIC ->
in_img SEGS a /\ ~ Exists (in_zr a) (as_owned_static B) /\ ~ (as_errno B <= a < as_errno B + 4).
Proof.
intros a HP. split; [exact (cmd_prog_img a HP)|].
assert (HP' : Exists (in_zr a) (as_prog_static B)) by (rewrite (ts_prog B HB); exact HP).
destruct (prog_static_sep B a (ts_ok B HB) HP') as (H1 & H2 & _). split; assumption.
Qed.
(* a callee's journal keeps a byte of the program's statics outside its footprint *)
Lemma lrfb_callee_keeps_PG : forall STK1 sp1 FP1 lyc Sc (W : world SEGS) memc mdc own ly2 S2 (W2 : world SEGS) mem2 md2 k1 a,
ajournal SEGS B STK1 sp1 FP1 lyc Sc W memc mdc own ly2 S2 W2 mem2 md2 k1 -> ~ YI16.sink_open_fp FP1 ->
~ inFP FP1 a -> Exists (in_zr a) TFIB_PROG_STATIC -> rdW W2 mem2 a = rdW W memc a.
Proof.
intros STK1 sp1 FP1 lyc Sc W memc mdc own ly2 S2 W2 mem2 md2 k1 a HJ Hso Hfp HP.
pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HIMG & _).
destruct (lrfb_PG_unowned a HP) as (Himg & Hown & Herr).
apply HIMG; [exact Himg | exact Hown | exact Herr |]. split; [intros H; exfalso; exact (Hso H) | exact Hfp].
Qed.
Lemma lrfb_region_kept_PG : forall E (W W2 : world SEGS) m m2 nn b lo hi wlo whi cs,
bv_unsigned (ew E nn) = b ->
(forall a, b + lo <= a < b + hi -> rdW W2 m2 a = rdW W m a) ->
(forall a, b + wlo <= a < b + whi -> writable_at SEGS (mrestrict (w_H W2) m2) a) ->
region_kept SEGS E (mrestrict (w_H W) m) (mrestrict (w_H W2) m2) (YP09.mkRegion (Some nn) lo hi wlo whi cs).
Proof.
intros E W W2 m m2 nn b lo hi wlo whi cs U Hv Hw.
split; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi base_val]; rewrite U.
- intros a Ha. apply (mbyte_of_aview SEGS). exact (Hv a Ha).
- intros a Ha _. exact (Hw a Ha).
Qed.

(* ---- the executor's frames ------------------------------------------------------------------------------ *)
(* a word of the frame the prologue wrote: the entry value of a callee-saved register *)
Lemma lrfb_frame_word : forall E m lo hi wlo whi cs sp (regs : bvmap 5 word) k (r : bv 5) off,
region_ok SEGS E m (YP09.mkRegion (Some 2%nat) lo hi wlo whi cs) -> bv_unsigned (ew E 2) = sp ->
In (YP09.mkChunk off (CVal 8 (SOff k 0))) cs -> ew E k = getr regs r ->
val_mem SEGS m (sp + off) 8 (bv_unsigned (getr regs r)).
Proof.
intros E m lo hi wlo whi cs sp regs k r off HR Hsp Hin Hk.
apply (field_of_region E m 2 sp cs lo hi wlo whi off 8 (SOff k 0) _ HR Hsp Hin); [| | cbn; lia].
- cbn [sv_denot]. rewrite Hk, Z.add_0_r. reflexivity.
- pose proof (bv_unsigned_in_range 64 (getr regs r)) as H. change (bv_modulus 64) with (2 ^ 64) in H. exact H.
Qed.


(* ---- the recorder's representation over readers that agree ------------------------------------------------ *)
Lemma lrfb_rep_set : forall ly S rd rd' R O h,
rec_repA B ly S rd R O ->
(forall a, A_G_REC <= a < A_G_REC + REC_SIZE -> ~ (A_G_REC + OFF_STATE <= a < A_G_REC + OFF_STATE + 8) -> rd' a = rd a) ->
(forall a, A_REC_SPILL <= a < A_REC_SPILL + SC_SIZE -> rd' a = rd a) ->
(forall pn i, In pn O -> 0 <= i < snd pn -> rd' (fst pn + i) = rd (fst pn + i)) ->
aval_mem rd' (A_G_REC + OFF_STATE) 8 h -> 0 <= h < 2 ^ 64 ->
rec_repA B ly S rd' (set_state R h) O.
Proof.
intros ly S rd rd' R O h (Q & HA & HOQ) Hg Hs Hb Hst Hh. exists Q. split; [|exact HOQ].
apply (lrfb_arep_set_state (ablocks B ly S) rd rd' R Q h HA).
- intros i Hi. apply Hg; unfold OFF_STATE, REC_SIZE in *; lia.
- intros i Hi. apply Hg; unfold OFF_HOST, OFF_STATE, REC_SIZE in *; lia.
- intros i Hi. apply Hs. lia.
- intros pn Hpn i Hi. apply Hb; [apply HOQ; exact Hpn | exact Hi].
- exact Hst.
- exact Hh.
Qed.
Lemma lrfb_set_state_id : forall R, set_state R (r_state R) = R.
Proof. intros [a b c d e f g h i]. reflexivity. Qed.
Lemma lrfb_rep_keep : forall ly S rd rd' R O,
rec_repA B ly S rd R O ->
(forall a, A_G_REC <= a < A_G_REC + REC_SIZE -> rd' a = rd a) ->
(forall a, A_REC_SPILL <= a < A_REC_SPILL + SC_SIZE -> rd' a = rd a) ->
(forall pn i, In pn O -> 0 <= i < snd pn -> rd' (fst pn + i) = rd (fst pn + i)) ->
rec_repA B ly S rd' R O.
Proof.
intros ly S rd rd' R O HR Hg Hs Hb.
pose proof HR as (Q & (_ & _ & _ & _ & _ & _ & (_ & _ & _ & Vs & _ & _ & _ & _ & Rs & _) & _) & _).
rewrite <- (lrfb_set_state_id R). apply (lrfb_rep_set ly S rd rd' R O (r_state R) HR).
- intros a Ha _. exact (Hg a Ha).
- exact Hs.
- exact Hb.
- apply (lrfb_aval_mem_kept rd); [exact Vs|]. intros k Hk. apply Hg. unfold A_G_REC, OFF_STATE, REC_SIZE. lia.
- exact Rs.
Qed.
(* below alloc_ceiling lie g_rec, record.spill and every live block *)
Lemma lrfb_rep_keep_low : forall ly S (W W' : world SEGS) mem mem' md R O,
AR SEGS B ly S W mem md -> rec_repA B ly S (rdW W mem) R O ->
(forall a, 0 <= a < alloc_ceiling -> rdW W' mem' a = rdW W mem a) ->
rec_repA B ly S (rdW W' mem') R O.
Proof.
intros ly S W W' mem mem' md R O HAR HR Hk.
pose proof asan_consts as (C1 & _).
apply (lrfb_rep_keep ly S (rdW W mem) (rdW W' mem') R O HR).
- intros a Ha. apply Hk. unfold A_G_REC, REC_SIZE in Ha. lia.
- intros a Ha. apply Hk. unfold A_REC_SPILL, SC_SIZE in Ha. lia.
- intros [p n] i Hin Hi. cbn [fst snd] in Hi |- *.
  destruct (al_blocks _ _ LAWS _ _ _ _ _ p n HAR (lrfb_rep_O_in ly S _ R O HR (p, n) Hin)) as (_ & H4 & Hc & _ & _ & _ & Hn).
  pose proof (req_size_pos n ltac:(lia)) as [_ Hq]. apply Hk. lia.
Qed.
(* the call record() makes in its slot *)
Lemma lrfb_rep_acall : forall ly S rd R fn A O, rec_repA B ly S rd (rec_record R fn A) O ->
exists P, acall_at (ablocks B ly S) rd (rec_slot R) (fn, A) P.
Proof.
intros ly S rd R fn A O (Q & (_ & _ & _ & HC & _) & _).
destruct HC as (Hlen & HlenQ & _ & Hcalls & Hspill & _).
revert Hlen HlenQ Hcalls Hspill. unfold rec_slot, rec_record.
destruct (Nat.ltb_spec (length (r_calls R)) 16) as [Hlt | Hge]; intros Hlen HlenQ Hcalls Hspill.
- cbn [r_calls set_calls] in Hlen, HlenQ, Hcalls. rewrite length_app in HlenQ. cbn [length] in HlenQ.
  destruct (nth_error (l_calls Q) (length (r_calls R))) as [P|] eqn:EP.
  + exists P. assert (Hn : nth_error (r_calls R ++ [(fn, A)]) (length (r_calls R)) = Some (fn, A)).
    { rewrite nth_error_app2 by lia. rewrite Nat.sub_diag. reflexivity. }
    exact (proj1 (Hcalls _ _ _ Hn EP)).
  + apply nth_error_None in EP. lia.
- cbn [r_spill set_spill] in Hspill. exists (l_spill Q). exact Hspill.
Qed.

(* ---- the string arg_s copies, at the state of the call ---------------------------------------------------- *)
(* uri, or the literal "*" when uri is NULL; the A walk's lrf_xs_arg *)
Lemma lrfb_xs_arg : forall ly S (W : world SEGS) mem md ly1 S1 (W1 : world SEGS) mem1 md1 STK sp0 own k pu uri O F,
AR SEGS B ly S W mem md -> ajournal SEGS B STK sp0 (lrfb_FP O) ly S W mem md own ly1 S1 W1 mem1 md1 k ->
(forall pn, In pn O -> In pn (ablocks B ly S)) ->
Permutation (ablocks B ly S) (ablocks B ly1 S1 ++ F) -> (forall pn, In pn F -> In pn O) ->
arodata_okP SEGS RLO RHI B (rdW W mem) ->
astr_argA B ly S (rdW W mem) (in_roP SEGS RLO RHI) O pu uri ->
astr_argA B ly1 S1 (rdW W1 mem1) (in_roP SEGS RLO RHI) [] (lrfb_s pu) (Some (lrfb_x uri)) /\
atail_vis SEGS W1 mem1 (lrfb_s pu + Z.of_nat (length (lrfb_x uri))).
Proof.
intros ly S W mem md ly1 S1 W1 mem1 md1 STK sp0 own k pu uri O F HAR HJ HO HPERM HFO HROD HSTR.
pose proof (proj1 HJ) as HAR1.
pose proof (lrfb_aro_kept STK sp0 O ly S W mem md own ly1 S1 W1 mem1 md1 k HJ HAR HO HROD) as HROD1.
pose proof (cmd_ro_ok_of_aro ly1 S1 W1 mem1 md1 HAR1 HROD1) as [HROB HROT].
destruct uri as [x|].
- (* uri *)
  destruct HSTR as (Hp0 & Hx & Hn & [(HBLK & HAP) | (HRO & HZ & HHV & HEND)]).
  + destruct HBLK as (q & m & Hqm & Hq & Hqe).
    assert (HnO : ~ In (q, m) O).
    { intros HqO. pose proof (proj1 (Forall_forall _ _) HAP (q, m) HqO) as Hap. unfold iv_apart in Hap. cbn [fst snd] in Hap. lia. }
    assert (Hqm1 : In (q, m) (ablocks B ly1 S1)).
    { pose proof (Permutation_in _ HPERM Hqm) as H. apply in_app_or in H as [H|H]; [exact H | exfalso; exact (HnO (HFO _ H))]. }
    destruct (al_blocks _ _ LAWS _ _ _ _ _ q m HAR Hqm) as (_ & _ & _ & _ & _ & _ & Hm).
    pose proof (req_size_pos m ltac:(lia)) as [_ Hreq].
    assert (Hpu : lrfb_s pu = pu) by (unfold lrfb_s; destruct (Z.eqb_spec pu 0); [contradiction | reflexivity]).
    rewrite Hpu. cbn [lrfb_x darg]. split.
    * split; [exact Hp0|]. split.
      { apply (lrfb_rastr_kept (rdW W mem)); [exact Hx|]. intros i Hi.
        replace (pu + i) with (q + (pu - q + i)) by lia.
        apply (lrfb_kept_heap STK sp0 O ly S W mem md own ly1 S1 W1 mem1 md1 k q m); try assumption; lia. }
      split; [exact Hn|]. left. split; [|constructor]. exists q, m. split; [exact Hqm1 | lia].
    * apply (cmd_heap_tail_vis ly1 S1 W1 mem1 md1 q m); [exact HAR1 | exact Hqm1 | lia].
  + assert (Hpu : lrfb_s pu = pu) by (unfold lrfb_s; destruct (Z.eqb_spec pu 0); [contradiction | reflexivity]).
    rewrite Hpu. cbn [lrfb_x darg]. split.
    * split; [exact Hp0|]. split.
      { apply (lrfb_rastr_kept (rdW W mem)); [exact Hx|]. intros i Hi.
        destruct (HRO i Hi) as (Hro & Hown & Herr).
        exact (lrfb_kept_ro STK sp0 O ly S W mem md own ly1 S1 W1 mem1 md1 k (pu + i) HJ HAR HO Hro Hown Herr). }
      split; [exact Hn|]. right. split; [exact HRO|]. split; [exact HZ|]. split; [exact HHV | exact HEND].
    * intros a Ha. exact (HROT _ HEND a Ha).
- (* the literal "*" *)
  cbn in HSTR. subst pu. unfold lrfb_s, lrfb_x. cbn [darg Z.eqb].
  assert (HLIT : abytes_atR (rdW W1 mem1) 0x21fe0 RO_lit_21fe0).
  { clear - HROB. unfold cmd_ro_bytes in HROB.
    repeat match type of HROB with
    | abytes_atR _ 0x21fe0 _ /\ _ => exact (proj1 HROB)
    | _ /\ _ => apply proj2 in HROB
    end. }
  assert (Hlin : forall i, 0 <= i < 2 -> in_roP SEGS RLO RHI (0x21fe0 + i)).
  { pose proof CMD_RO_IN as HROIN. clear - HROIN. unfold cmd_ro_in in HROIN.
    repeat match type of HROIN with
    | (forall i, 0 <= i < 2 -> _ (0x21fe0 + i)) /\ _ => exact (proj1 HROIN)
    | _ /\ _ => apply proj2 in HROIN
    end. }
  assert (HEND : In (0x21fe0 + Z.of_nat (length (bstr "*"))) cmd_ro_ends) by (apply In_of_existsb; vm_compute; reflexivity).
  split.
  + split; [lia|]. split.
    { split; [exact HLIT | cbn; intros [H|[]]; vm_compute in H; discriminate H]. }
    split; [cbn; unfold LMAX; lia|]. right. split.
    { intros i Hi. apply lrfb_star_unowned; [cbn in Hi; lia | apply Hlin; cbn in Hi; lia]. }
    split; [vm_compute; reflexivity|]. split; [vm_compute; reflexivity | exact HEND].
  + intros a Ha. exact (HROT _ HEND a Ha).
Qed.

(* the bytes record() may write lie below alloc_ceiling *)
Lemma lrfb_rec_fp_low : forall ly S (W : world SEGS) mem md R O a, AR SEGS B ly S W mem md ->
(forall pn, In pn O -> In pn (ablocks B ly S)) ->
inFP ((A_G_REC + OFF_NCALLS, A_G_REC + OFF_NCALLS + 4) :: (rec_slot R, rec_slot R + 8) ::
      (if Nat.ltb (length (r_calls R)) 16 then [] else ablocks_fp O)) a -> 0 <= a < alloc_ceiling.
Proof.
intros ly S W mem md R O a HAR HO (r & Hr & Ha). pose proof asan_consts as (C1 & _).
destruct Hr as [<- | [<- | Hr]]; cbn [fst snd] in Ha.
- unfold A_G_REC, OFF_NCALLS in Ha. lia.
- pose proof (lrfb_slot_in R a ltac:(unfold CALL_SIZE; lia)) as Hs.
  unfold A_G_REC, OFF_CALLS, OFF_ANSWER, A_REC_SPILL, SC_SIZE in Hs. lia.
- revert Hr. destruct (Nat.ltb (length (r_calls R)) 16); intros Hr; [destruct Hr|].
  destruct (inFP_ablocks_fp_inv O a (ex_intro _ r (conj Hr Ha))) as (p & n & HpO & Hpa).
  destruct (al_blocks _ _ LAWS _ _ _ _ _ p n HAR (HO _ HpO)) as (_ & H4 & Hpc & _). lia.
Qed.
(* the bytes arg_s may write: c->nargs and c->args[0] of the slot *)
Lemma lrfb_arg_fp_in : forall R a,
inFP (if Z.of_nat (length (@nil (list byte))) <? REC_ARGS_MAX
      then [(rec_slot R + CALL_OFF_NARGS, rec_slot R + CALL_OFF_NARGS + 4);
            (rec_slot R + CALL_OFF_ARGS + 8 * Z.of_nat (length (@nil (list byte))),
             rec_slot R + CALL_OFF_ARGS + 8 * Z.of_nat (length (@nil (list byte))) + 8)]
      else []) a ->
(A_G_REC + OFF_CALLS <= a < A_G_REC + OFF_ANSWER) \/ (A_REC_SPILL <= a < A_REC_SPILL + SC_SIZE).
Proof.
intros R a (r & Hr & Ha). cbn [length Z.of_nat] in Hr. change (0 <? REC_ARGS_MAX) with true in Hr.
destruct Hr as [<- | [<- | []]]; cbn [fst snd] in Ha; apply (lrfb_slot_in R a);
unfold CALL_OFF_NARGS, CALL_OFF_ARGS, CALL_SIZE in *; lia.
Qed.

(* ---- the walk -------------------------------------------------------------------------------------------- *)
Theorem tlv2_refusals_forget_holds : tlv2_refusals_forget_spec B MT.
Proof.
unfold tlv2_refusals_forget_spec.
intros ly S W regs mem md ch pu uri R O HPRE HROD HROOK H10 Hpu64 HSTR HTAIL HREP HEV HLIVE HMOK.
pose proof pa_B_ok as HBASE.
pose proof HPRE as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (HSTKv : LV2_REFUSALS_FORGET_STK = 16592) by (vm_compute; reflexivity).
assert (HRSv : RECORD_STK = 16560) by (vm_compute; reflexivity).
assert (HASv : ARG_S_STK = 16464) by (vm_compute; reflexivity).
assert (HMSv : MIX_CALL_STK = 4192) by (vm_compute; reflexivity).
assert (HO : forall pn, In pn O -> In pn (ablocks B ly S)) by exact (lrfb_rep_O_in ly S _ R O HREP).
assert (Hh : 0 <= r_state R < 2 ^ 64).
{ destruct HREP as (Q0 & (_ & _ & _ & _ & _ & _ & (_ & _ & _ & _ & _ & _ & _ & _ & Hs & _) & _) & _). exact Hs. }
assert (Hs64 : 0 <= lrfb_s pu < 2 ^ 64) by (unfold lrfb_s; destruct (pu =? 0); lia).
(* the entry state: every register its own atom, g_rec.state's value at atom 32, the string's address at atom 33 *)
pose proof (ajournal_init SEGS B LV2_REFUSALS_FORGET_STK (lrfb_FP O) ly S W regs mem md ch HPRE) as HJ.
remember (Eimg (Ereg regs (lrfb_extra (r_state R) (lrfb_s pu)))) as E eqn:HE.
assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (HAE : env_agree 32 (Ereg regs (lrfb_extra (r_state R) (lrfb_s pu))) E)
  by (rewrite HE; split; [intros n Hn; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
assert (EE : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E n = getr regs r).
{ intros n r Hn. rewrite HE. pose proof (bv_unsigned_in_range 5 r) as Hr5. change (bv_modulus 5) with 32 in Hr5.
  rewrite Eimg_low by (unfold A_TEXT; lia). apply ew_Ereg_nat. exact Hn. }
assert (E32 : ew E 32 = Z_to_bv 64 (r_state R)) by (rewrite HE, Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 0)).
assert (E33 : ew E 33 = Z_to_bv 64 (lrfb_s pu)) by (rewrite HE, Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 1)).
assert (Usp : bv_unsigned (ew E 2) = spZ regs) by (rewrite (EE 2%nat 2%bv eq_refl); reflexivity).
assert (HS : st_ok_pi SEGS VAL E lrfb_ss0
  (restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + AF_lv2_refusals_forget)) mem (seg_rom SEGS)))).
{ rewrite restrict_mkst_fx. apply pa_entry_st_ok_full.
  - rewrite HE. apply regs_ok_Eimg_Ereg.
  - vm_compute. reflexivity.
  - unfold stack_region. repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
    rewrite Usp. split; [lia|]. split; [lia|]. split; [|constructor].
    intros o Ho. apply (apresent_writable SEGS). apply Hpres. rewrite HSTKv. lia.
  - apply pairwise_disjoint_of_extents. unfold stack_region, extent_of_region.
    cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val]. cbn [zpairwise_disjoint zall_disjoint]. repeat split; exact I.
  - split; [|split; [exact I | exact I]]. cbn [lrfb_facts0 f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
    rewrite Usp. try change (2 ^ 4) with 16. try change (2 ^ 46) with 70368744177664. try change (2 ^ 47) with 140737488355328.
    repeat match goal with |- _ /\ _ => split end; first [exact I | lia]. }
clear HE.
unfold cfg_at. change (w64 (BASE + AF_lv2_refusals_forget)) with (Z_to_bv 64 (BASE + AF_lv2_refusals_forget)).
(* 0x8cd54 .. 0x8cd6c: the prologue, s1 := uri, a0 := 25, the call of record *)
paj_run_shc RUNP RUNC HS HJ.
{ lazymatch goal with |- awr_ok _ _ ?Ex ?rs ?stk ?spx ?fp ?b0 ?bc ?fr ?lyx ?own =>
  let rs' := eval vm_compute in rs in change (awr_ok SEGS B Ex rs' stk spx fp b0 bc fr lyx own) end.
  eapply awr_ok_cons_stack; [reflexivity | exact Usp | cbn [YP09.r_wlo]; lia | cbn [YP09.r_whi]; lia | apply awr_ok_nil]. }
clear HF HG. rename HFr into HFr1. rename ms into ms1.
prreg HS (10%bv : bv 5) R10. prreg HS (2%bv : bv 5) R2. prreg HS (3%bv : bv 5) R3. prreg HS (4%bv : bv 5) R4.
prreg HS (1%bv : bv 5) R1. prreg HS (8%bv : bv 5) R8.
assert (Esp1 : spZ (ms_regs ms1) = spZ regs + -32) by (unfold spZ at 1; rewrite R2, Usp; apply unsigned_lit_small; lia).
assert (Hkeep1 : forall a, 0 <= a < alloc_ceiling -> rdW W (ms_mem ms1) a = rdW W mem a).
{ intros a Ha. apply (recb_run_keeps_m (PI := PI) E _ (w_H W) mem (ms_mem ms1) a HFr1); [lia|].
  intros (r & Hr' & Hw). vm_compute in Hr'.
  repeat (destruct Hr' as [Hr' | Hr']; [subst r; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hw; rewrite ?Usp in Hw; lia|]).
  destruct Hr'. }
pose proof (lrfb_aro_kept _ _ O ly S W mem md _ ly S W (ms_mem ms1) _ _ HJ HAR HO HROD) as HROD1.
pose proof (lrfb_rep_keep_low ly S W W mem (ms_mem ms1) md R O HAR HREP Hkeep1) as HREP1.
assert (Hs0 : s0Z (ms_regs ms1) = s0Z regs) by (unfold s0Z; rewrite R8, (EE 8%nat 8%bv eq_refl); reflexivity).
(* s0 at the call of record is the entry's (class A, a Theorem Labs lane's S0-SITES.md): afn_pre's chain, kept above the entry sp
   (the prologue writes only below it) and lowered to the call's sp *)
assert (Hch1 : achain ly (aview SEGS (w_H W) (ms_mem ms1)) (spZ regs + -32) (s0Z (ms_regs ms1)) ch).
{ rewrite Hs0. apply (achain_lower ly _ (spZ regs) _ _ ch); [|lia].
  apply (achain_kept ly (aview SEGS (w_H W) mem) _ (spZ regs) (s0Z regs) ch (spZ regs) Hch ltac:(lia) ltac:(lia)).
  intros a Ha. apply (recb_run_keeps_m (PI := PI) E _ (w_H W) mem (ms_mem ms1) a HFr1); [lia|].
  intros (r & Hr' & Hw). vm_compute in Hr'.
  repeat (destruct Hr' as [Hr' | Hr']; [subst r; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hw; rewrite ?Usp in Hw; lia|]).
  destruct Hr'. }
assert (HEVr : st_nev S + EV_RECORD R <= EV_MAX) by (unfold EV_LV2_REFUSALS_FORGET, EV_ARG_S, EV_XMALLOC in HEV; lia).
assert (HXMa : 0 <= XM_ARG_S MT (Some (darg uri (bstr "*"%string)))).
{ unfold XM_ARG_S, XM_XMALLOC, LIVE_XMALLOC. apply (mo_malloc_nonneg MT MTL). lia. }
assert (HMOKr : mo_ok MT S (XM_RECORD MT R)).
{ apply (mo_ok_le MT MTL S (XM_RECORD MT R) (XM_LV2_REFUSALS_FORGET MT R uri) HMOK). unfold XM_LV2_REFUSALS_FORGET. lia. }
pmkst HS. rewrite (CmdRecAns.rca_sig_record (PI := PI) cmd_sig_prog_PB).
eapply SRr_bind.
{ eapply (cl_callS_wide B LAWS W (ms_regs ms1) (ms_mem ms1) _ LV2_REFUSALS_FORGET_STK (spZ regs) (lrfb_FP O) ly S W mem md []
    ly S _ 0 RECORD_STK _ (EV_RECORD R) (-32) (getr (ms_regs ms1) 1) ch _ HJ).
  - exact Esp1.
  - reflexivity.
  - lia.
  - rewrite HRSv. lia.
  - rewrite HRSv, HSTKv. lia.
  - rewrite R3, (EE 3%nat 3%bv eq_refl). exact Hgp.
  - rewrite R4, (EE 4%nat 4%bv eq_refl). exact Htp.
  - reflexivity.
  - rewrite R1. apply ret_ok_codeptr_v; [lia | reflexivity].
  - rewrite R1, unsigned_lit_small by lia. lia.
  - exact Hch1.
  - intros HPRE1. eapply SRr_mono.
    { apply (TRECORD fx ly S W (ms_regs ms1) (ms_mem ms1) _ ch REC_LV2_REFUSALS_FORGET R O HPRE1 HROD1).
      - rewrite R10. reflexivity.
      - unfold REC_LV2_REFUSALS_FORGET, REC_FN_COUNT. lia.
      - exact HREP1.
      - exact HEVr.
      - exact HMOKr. }
    intros W2 c2 _ Hc2. exact Hc2.
  - intros a Ha. destruct Ha as (r & Hr & Ha). destruct Hr as [<- | [<- | Hr]]; cbn [fst snd] in Ha.
    + apply lrfb_awr_PG; [apply lrfb_inFP_grec | apply lrfb_in_PG_grec]; unfold OFF_NCALLS, REC_SIZE in *; lia.
    + destruct (lrfb_slot_in R a ltac:(unfold CALL_SIZE; lia)) as [Hg | Hsp].
      * apply lrfb_awr_PG; [apply lrfb_inFP_grec | apply lrfb_in_PG_grec]; unfold OFF_CALLS, OFF_ANSWER, REC_SIZE in *; lia.
      * apply lrfb_awr_PG; [apply lrfb_inFP_spill | apply lrfb_in_PG_spill]; lia.
    + revert Hr. destruct (Nat.ltb (length (r_calls R)) 16); intros Hr; [destruct Hr|].
      destruct (inFP_ablocks_fp_inv O a (ex_intro _ r (conj Hr Ha))) as (p & n & HpO & Hpa).
      right. left. split; [exists r; split; [right; right; exact Hr | exact Ha]|].
      exists p, n. split; [exact (HO _ HpO) | exact Hpa].
  - intros ly2 S2 W2 regs2 mem2 md2 _ a Ha Hw _. exfalso.
    pose proof (lrfb_rec_fp_low ly S W mem md R O a HAR HO Ha). lia. }
cbv beta. intros W2 c2 Hwle2 (ly2 & S2 & regs2 & mem2 & md2 & -> & HJ2 & HJc2 & HP2 &
  (F & O1 & Ha02 & Hperm2 & HlenF & HFO & HREP2 & HO1 & HBB2 & MLE2)).
rewrite R1.
jafter_call_keep_pi HS 48%nat regs2 (mrestrict (w_H W2) mem2) HP2 [0]%nat HS2.
match type of HS2 with ?t -> _ => assert (HRK : t); [|specialize (HS2 HRK); clear HRK] end.
{ cbn [ms_mem restrict]. repeat apply Forall_cons; [| apply Forall_nil].
  eapply (lrfb_region_kept_hi2 SEGS E (w_H W) (w_H W2) (ms_mem ms1) mem2 2 (spZ regs)); [exact Usp | |].
  - intros a Ha. pose proof HJc2 as (_ & _ & _ & _ & _ & _ & _ & _ & K9 & _).
    apply K9; [lia | rewrite HRSv; lia |].
    intros Hf. pose proof (lrfb_rec_fp_low ly S W mem md R O a HAR HO Hf). lia.
  - intros a Ha. pose proof HJ2 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HP14 & _).
    apply HP14. rewrite HSTKv. lia. }
clear HS R10 R2 R3 R4 R1 R8. rewrite <- restrict_mkst_fx in HS2. rename HS2 into HS.
remember (havoc E 48 (map (getr regs2) CLOB)) as E2 eqn:HE2 in HS.
assert (HEI2 : img_env VAL A_LIM E2) by (rewrite HE2; apply img_env_havoc; [exact HEI | cbv; lia]).
assert (OLD2 : forall n, (n < 48)%nat -> ew E2 n = ew E n) by (intros n Hn; rewrite HE2; apply YN3v.ew_havoc_old; exact Hn).
assert (HAE2 : env_agree 32 (Ereg regs (lrfb_extra (r_state R) (lrfb_s pu))) E2)
  by (rewrite HE2; apply env_agree_havoc_ge; [cbv; lia | exact HAE]).
assert (E52 : ew E2 52 = getr regs2 10) by (rewrite HE2; reflexivity).
clear HE2.
assert (Usp2 : bv_unsigned (ew E2 2) = spZ regs) by (rewrite OLD2 by lia; exact Usp).
pose proof (proj1 HJ2) as HAR2m.
(* 0x8cd70 .. 0x8cd74: s0 := the slot, then the branch on uri *)
paj_run_shc RUNP RUNC HS HJ2.
{ lazymatch goal with |- awr_ok _ _ ?Ex ?rs ?stk ?spx ?fp ?b0 ?bc ?fr ?lyx ?own =>
  let rs' := eval vm_compute in rs in change (awr_ok SEGS B Ex rs' stk spx fp b0 bc fr lyx own) end.
  eapply awr_ok_cons_stack; [reflexivity | exact Usp2 | cbn [YP09.r_wlo]; lia | cbn [YP09.r_whi]; lia | apply awr_ok_nil]. }
clear HF HG. rename HFr into HFr2. rename ms into ms2.
assert (Hkeep2 : forall a, 0 <= a < alloc_ceiling -> rdW W2 (ms_mem ms2) a = rdW W2 mem2 a).
{ intros a Ha. apply (recb_run_keeps_m (PI := PI) E2 _ (w_H W2) mem2 (ms_mem ms2) a HFr2); [lia|].
  intros (r & Hr' & Hw). vm_compute in Hr'.
  repeat (destruct Hr' as [Hr' | Hr']; [subst r; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hw; rewrite ?Usp2 in Hw; lia|]).
  destruct Hr'. }
lazymatch goal with |- SRr _ _ _ ?Q =>
enough (CONT : forall msX mdX, st_ok_pi SEGS VAL E2 lrfb_ssC (restrict (w_H W2) msX) ->
  ajournal SEGS B LV2_REFUSALS_FORGET_STK (spZ regs) (lrfb_FP O) ly S W mem md [] ly2 S2 W2 (ms_mem msX) mdX (0 + EV_RECORD R) ->
  (forall a, 0 <= a < alloc_ceiling -> rdW W2 (ms_mem msX) a = rdW W2 mem2 a) ->
  SRr SEGS W2 (mkCfg msX mdX) Q) end.
{ (* the two arms of `bnez s1` at 0x8cd74, joined at the call of arg_s *)
  assert (E10 : ew E2 10 = Z_to_bv 64 pu) by (rewrite OLD2 by lia; rewrite (EE 10%nat 10%bv eq_refl); exact H10).
  assert (U10 : U E2 (SOff 10 0) = pu) by exact (lrfb_U_atom E2 10 pu E10 Hpu64).
  psrr_branch_pi RUNP BR HS.
  - (* uri <> NULL: s1 = uri *)
    rewrite branch_ne_U, U10 in Hc. change (U E2 (SLit 0)) with 0 in Hc. apply Bool.negb_true_iff, Z.eqb_neq in Hc.
    paj_run_to_sh RUNTOP HS HJ2 L_ARG_CALL.
    { lazymatch goal with |- awr_ok _ _ ?Ex ?rs ?stk ?spx ?fp ?b0 ?bc ?fr ?lyx ?own =>
      let rs' := eval vm_compute in rs in change (awr_ok SEGS B Ex rs' stk spx fp b0 bc fr lyx own) end.
      eapply awr_ok_cons_stack; [reflexivity | exact Usp2 | cbn [YP09.r_wlo]; lia | cbn [YP09.r_whi]; lia | apply awr_ok_nil]. }
    assert (Hv : sv_denot E2 (SOff 10 0) = sv_denot E2 (SOff L_S 0)).
    { cbn [sv_denot]. change L_S with 33%nat. rewrite E10, (OLD2 33%nat ltac:(lia)), E33.
      unfold lrfb_s. rewrite (proj2 (Z.eqb_neq pu 0) Hc). reflexivity. }
    pose proof (lrfb_canon_ok E2 _ _ (SOff 10 0) HS ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
      ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) Hv) as HSC.
    apply (CONT _ _ HSC HJ2). intros a Ha. rewrite <- (Hkeep2 a Ha).
    apply (recb_run_keeps_m (PI := PI) E2 _ (w_H W2) (ms_mem ms2) (ms_mem ms) a HFr); [lia|].
    intros (r & Hr' & Hw). vm_compute in Hr'.
    repeat (destruct Hr' as [Hr' | Hr']; [subst r; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hw; rewrite ?Usp2 in Hw; lia|]).
    destruct Hr'.
  - (* uri = NULL: s1 = "*" *)
    rewrite branch_ne_U, U10 in Hc. change (U E2 (SLit 0)) with 0 in Hc. apply Bool.negb_false_iff, Z.eqb_eq in Hc.
    paj_run_to_sh RUNTOP HS HJ2 L_ARG_CALL.
    { lazymatch goal with |- awr_ok _ _ ?Ex ?rs ?stk ?spx ?fp ?b0 ?bc ?fr ?lyx ?own =>
      let rs' := eval vm_compute in rs in change (awr_ok SEGS B Ex rs' stk spx fp b0 bc fr lyx own) end.
      eapply awr_ok_cons_stack; [reflexivity | exact Usp2 | cbn [YP09.r_wlo]; lia | cbn [YP09.r_whi]; lia | apply awr_ok_nil]. }
    assert (Hv : sv_denot E2 (SOff 330 0) = sv_denot E2 (SOff L_S 0)).
    { cbn [sv_denot]. change L_S with 33%nat. rewrite (OLD2 33%nat ltac:(lia)), E33.
      rewrite (img_env_atomP E2 330 HEI2 ltac:(unfold A_TEXT, A_LIM; lia)).
      change 330%nat with (A_OBJ 89). rewrite lrfb_star_val. unfold lrfb_s. rewrite Hc. reflexivity. }
    pose proof (lrfb_canon_ok E2 _ _ (SOff 330 0) HS ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
      ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) Hv) as HSC.
    apply (CONT _ _ HSC HJ2). intros a Ha. rewrite <- (Hkeep2 a Ha).
    apply (recb_run_keeps_m (PI := PI) E2 _ (w_H W2) (ms_mem ms2) (ms_mem ms) a HFr); [lia|].
    intros (r & Hr' & Hw). vm_compute in Hr'.
    repeat (destruct Hr' as [Hr' | Hr']; [subst r; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hw; rewrite ?Usp2 in Hw; lia|]).
    destruct Hr'. }
clear HS. intros msX mdX HSX HJX HKX.
(* 0x8cd88: the call of arg_s on the slot and the string *)
paj_run_shc RUNP RUNC HSX HJX.
{ lazymatch goal with |- awr_ok _ _ ?Ex ?rs ?stk ?spx ?fp ?b0 ?bc ?fr ?lyx ?own =>
  let rs' := eval vm_compute in rs in change (awr_ok SEGS B Ex rs' stk spx fp b0 bc fr lyx own) end.
  eapply awr_ok_cons_stack; [reflexivity | exact Usp2 | cbn [YP09.r_wlo]; lia | cbn [YP09.r_whi]; lia | apply awr_ok_nil]. }
clear HF HG. rename HFr into HFr3. rename ms into ms3.
prreg HSX (10%bv : bv 5) R10. prreg HSX (11%bv : bv 5) R11. prreg HSX (2%bv : bv 5) R2. prreg HSX (3%bv : bv 5) R3.
prreg HSX (4%bv : bv 5) R4. prreg HSX (1%bv : bv 5) R1. prreg HSX (8%bv : bv 5) R8.
assert (Esp3 : spZ (ms_regs ms3) = spZ regs + -32) by (unfold spZ at 1; rewrite R2, Usp2; apply unsigned_lit_small; lia).
assert (Hkeep3 : forall a, 0 <= a < alloc_ceiling -> rdW W2 (ms_mem ms3) a = rdW W2 mem2 a).
{ intros a Ha. rewrite <- (HKX a Ha). apply (recb_run_keeps_m (PI := PI) E2 _ (w_H W2) (ms_mem msX) (ms_mem ms3) a HFr3); [lia|].
  intros (r & Hr' & Hw). vm_compute in Hr'.
  repeat (destruct Hr' as [Hr' | Hr']; [subst r; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hw; rewrite ?Usp2 in Hw; lia|]).
  destruct Hr'. }
pose proof (proj1 HJX) as HAR3.
pose proof (lrfb_rep_keep_low ly2 S2 W2 W2 mem2 (ms_mem ms3) md2 _ O1 HAR2m HREP2 Hkeep3) as HREP3.
pose proof (lrfb_aro_kept _ _ O ly S W mem md _ ly2 S2 W2 (ms_mem ms3) _ _ HJX HAR HO HROD) as HROD3.
pose proof (cmd_ro_ok_of_aro ly2 S2 W2 (ms_mem ms3) _ HAR3 HROD3) as HROOK3.
pose proof (lrfb_xs_arg ly S W mem md ly2 S2 W2 (ms_mem ms3) _ _ _ _ _ pu uri O F HAR HJX HO Hperm2 HFO HROD HSTR)
  as (HSTR3 & HTAIL3).
assert (Hslot : 0 <= rec_slot R < alloc_ceiling).
{ pose proof (lrfb_slot_in R (rec_slot R) ltac:(unfold CALL_SIZE; lia)) as Hsl.
  unfold A_G_REC, OFF_CALLS, OFF_ANSWER, A_REC_SPILL, SC_SIZE in Hsl. lia. }
assert (Hs08 : s0Z (ms_regs ms3) = rec_slot R) by (unfold s0Z; rewrite R8, E52, Ha02; apply unsigned_lit_small; lia).
assert (HEVa : st_nev S2 + EV_ARG_S <= EV_MAX).
{ pose proof HJX as (_ & _ & _ & _ & _ & _ & Hn3 & _). unfold EV_LV2_REFUSALS_FORGET in HEV. lia. }
assert (HLIVEa : blocks_bytes S2 + LIVE_ARG_S (Some (lrfb_x uri)) <= LIVE_MAX)
  by (unfold LIVE_LV2_REFUSALS_FORGET in HLIVE; unfold lrfb_x; lia).
assert (HMOKa : mo_ok MT S2 (XM_ARG_S MT (Some (lrfb_x uri)))).
{ apply (mo_ok_step MT MTL S S2 (XM_RECORD MT R) _); [|exact MLE2]. unfold XM_LV2_REFUSALS_FORGET in HMOK. exact HMOK. }
pmkst HSX. rewrite lrfb_sig_arg_s.
eapply SRr_bind.
{ eapply (cl_callS_wide B LAWS W2 (ms_regs ms3) (ms_mem ms3) _ LV2_REFUSALS_FORGET_STK (spZ regs) (lrfb_FP O) ly S W mem md []
    ly2 S2 _ (0 + EV_RECORD R) ARG_S_STK _ EV_ARG_S (-32) (getr (ms_regs ms3) 1) [] _ HJX).
  - exact Esp3.
  - reflexivity.
  - lia.
  - rewrite HASv. lia.
  - rewrite HASv, HSTKv. lia.
  - rewrite R3, OLD2 by lia. rewrite (EE 3%nat 3%bv eq_refl). exact Hgp.
  - rewrite R4, OLD2 by lia. rewrite (EE 4%nat 4%bv eq_refl). exact Htp.
  - reflexivity.
  - rewrite R1. apply ret_ok_codeptr_v; [lia | reflexivity].
  - rewrite R1, unsigned_lit_small by lia. lia.
  - apply achain_low. rewrite Hs08. lia.
  - intros HPRE3. eapply SRr_mono.
    { apply (TARG_S fx ly2 S2 W2 (ms_regs ms3) (ms_mem ms3) _ [] (rec_slot R) (lrfb_s pu) REC_LV2_REFUSALS_FORGET []
        (Some (lrfb_x uri)) R O1 HPRE3 HROD3 HROOK3).
      - rewrite R10, E52. exact Ha02.
      - rewrite R11. change L_S with 33%nat. rewrite (OLD2 33%nat ltac:(lia)). exact E33.
      - reflexivity.
      - exact HREP3.
      - left. exact HSTR3.
      - intros x0 Hx0. injection Hx0 as <-. exact HTAIL3.
      - exact HEVa.
      - exact HLIVEa.
      - exact HMOKa. }
    intros W3 c3 _ Hc3. exact Hc3.
  - intros a Ha. destruct (lrfb_arg_fp_in R a Ha) as [Hg | Hsp].
    + apply lrfb_awr_PG; [apply lrfb_inFP_grec | apply lrfb_in_PG_grec]; unfold OFF_CALLS, OFF_ANSWER, REC_SIZE in *; lia.
    + apply lrfb_awr_PG; [apply lrfb_inFP_spill | apply lrfb_in_PG_spill]; lia.
  - intros ly3 S3 W3 regs3 mem3 md3 _ a Ha Hw _. exfalso.
    destruct (lrfb_arg_fp_in R a Ha) as [Hg | Hsp]; unfold A_G_REC, OFF_CALLS, OFF_ANSWER, A_REC_SPILL, SC_SIZE in *; lia. }
cbv beta. intros W3 c3 Hwle3 (ly3 & S3 & regs3 & mem3 & md3 & -> & HJ3 & HJc3 & HP3 & (HBB3 & MLE3 & HK3)).
destruct HK3 as [(Hlen6 & _) | (_ & p & Hp & Hperm3 & Hfresh3 & HREP4)];
  [exfalso; unfold REC_ARGS_MAX in Hlen6; cbn [length Z.of_nat] in Hlen6; lia|].
cbn [sarg app] in Hperm3, Hfresh3, HREP4.
set (n := Z.of_nat (length (lrfb_x uri)) + 1) in *.
assert (Hn1 : 1 <= n) by (unfold n; lia).
rewrite R1.
jafter_call_keep_pi HSX 64%nat regs3 (mrestrict (w_H W3) mem3) HP3 [0]%nat HS3.
match type of HS3 with ?t -> _ => assert (HRK : t); [|specialize (HS3 HRK); clear HRK] end.
{ cbn [ms_mem restrict]. repeat apply Forall_cons; [| apply Forall_nil].
  eapply (lrfb_region_kept_hi2 SEGS E2 (w_H W2) (w_H W3) (ms_mem ms3) mem3 2 (spZ regs)); [exact Usp2 | |].
  - intros a Ha. pose proof HJc3 as (_ & _ & _ & _ & _ & _ & _ & _ & K9 & _).
    apply K9; [lia | rewrite HASv; lia |].
    intros Hf. destruct (lrfb_arg_fp_in R a Hf) as [Hg | Hsp]; unfold A_G_REC, OFF_CALLS, OFF_ANSWER, A_REC_SPILL, SC_SIZE in *; lia.
  - intros a Ha. pose proof HJ3 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HP14 & _).
    apply HP14. rewrite HSTKv. lia. }
clear HSX R10 R11 R2 R3 R4 R1 R8.
remember (havoc E2 64 (map (getr regs3) CLOB)) as E3 eqn:HE3 in HS3.
assert (HEI3 : img_env VAL A_LIM E3) by (rewrite HE3; apply img_env_havoc; [exact HEI2 | cbv; lia]).
assert (OLD3 : forall n, (n < 64)%nat -> ew E3 n = ew E2 n) by (intros n' Hn'; rewrite HE3; apply YN3v.ew_havoc_old; exact Hn').
assert (HAE3 : env_agree 32 (Ereg regs (lrfb_extra (r_state R) (lrfb_s pu))) E3)
  by (rewrite HE3; apply env_agree_havoc_ge; [cbv; lia | exact HAE2]).
clear HE3.
assert (Usp3 : bv_unsigned (ew E3 2) = spZ regs) by (rewrite OLD3 by lia; exact Usp2).
(* g_rec.state's word for the load at 0x8cd90 *)
assert (Vst4 : aval_mem (rdW W3 mem3) (A_G_REC + OFF_STATE) 8 (r_state R)).
{ pose proof HREP4 as (Q4 & (_ & _ & _ & _ & _ & _ & (_ & _ & _ & Vs & _) & _) & _).
  rewrite lrfb_state_record in Vs. exact Vs. }
pose proof (st_ok_pi_add_region E3 _ _ lrfb_state_region HS3 eq_refl) as HS.
match type of HS with ?t -> _ => assert (HRK : t); [|specialize (HS HRK); clear HRK] end.
{ unfold region_ok, lrfb_state_region, obj8_region.
  cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val ms_mem mkst].
  rewrite (HEI3 (A_OBJ 86) ltac:(unfold A_OBJ, A_TEXT, A_LIM; lia)), lrfb_state_val.
  split; [unfold A_G_REC, OFF_STATE; lia|]. split; [unfold A_G_REC, OFF_STATE; lia|]. split; [intros o Ho; lia|].
  constructor; [|constructor].
  apply (chunk_ok_val SEGS E3 _ (A_G_REC + OFF_STATE) 0 8 (SOff L_H 0) (r_state R)).
  - cbn [sv_denot]. change L_H with 32%nat. rewrite OLD3, OLD2 by lia. rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity.
  - zside.
  - zside.
  - rewrite Z.add_0_r. exact (val_mem_view SEGS (w_H W3) mem3 _ _ _ Vst4). }
match type of HS with ?t -> _ => assert (HRK : t); [|specialize (HS HRK); clear HRK] end.
{ cbn [all_disjoint ss_mem]. split; [|exact I]. unfold extent_disjoint, lrfb_state_region, obj8_region.
  cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val].
  rewrite (HEI3 (A_OBJ 86) ltac:(unfold A_OBJ, A_TEXT, A_LIM; lia)), lrfb_state_val, Usp3.
  unfold A_G_REC, OFF_STATE. lia. }
lazymatch type of HS with st_ok_pi _ _ _ ?s _ => let v := eval vm_compute in s in change s with v in HS end.
clear HS3. rewrite <- restrict_mkst_fx in HS.
pose proof (proj1 HJ3) as HAR3m.
(* 0x8cd8c .. 0x8cd98: a0 := g_rec.state, a1 := the slot, the call of mix_call *)
paj_run_shc RUNP RUNC HS HJ3.
{ lazymatch goal with |- awr_ok _ _ ?Ex ?rs ?stk ?spx ?fp ?b0 ?bc ?fr ?lyx ?own =>
  let rs' := eval vm_compute in rs in change (awr_ok SEGS B Ex rs' stk spx fp b0 bc fr lyx own) end.
  apply awr_ok_cons_ro; [cbn; lia|].
  eapply awr_ok_cons_stack; [reflexivity | exact Usp3 | cbn [YP09.r_wlo]; lia | cbn [YP09.r_whi]; lia | apply awr_ok_nil]. }
clear HF HG. rename HFr into HFr4. rename ms into ms4.
prreg HS (10%bv : bv 5) R10. prreg HS (11%bv : bv 5) R11. prreg HS (2%bv : bv 5) R2. prreg HS (3%bv : bv 5) R3.
prreg HS (4%bv : bv 5) R4. prreg HS (1%bv : bv 5) R1. prreg HS (8%bv : bv 5) R8.
assert (Esp4 : spZ (ms_regs ms4) = spZ regs + -32) by (unfold spZ at 1; rewrite R2, Usp3; apply unsigned_lit_small; lia).
assert (UST3 : bv_unsigned (ew E3 (A_OBJ 86)) = A_G_REC + OFF_STATE)
  by (rewrite (HEI3 (A_OBJ 86) ltac:(unfold A_OBJ, A_TEXT, A_LIM; lia)); exact lrfb_state_val).
assert (Hkeep4 : forall a, 0 <= a < alloc_ceiling -> rdW W3 (ms_mem ms4) a = rdW W3 mem3 a).
{ intros a Ha. apply (recb_run_keeps_m (PI := PI) E3 _ (w_H W3) mem3 (ms_mem ms4) a HFr4); [lia|].
  intros (r & Hr' & Hw). vm_compute in Hr'.
  repeat (destruct Hr' as [Hr' | Hr']; [subst r; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hw; rewrite ?Usp3, ?UST3 in Hw; lia|]).
  destruct Hr'. }
pose proof (lrfb_rep_keep_low ly3 S3 W3 W3 mem3 (ms_mem ms4) md3 _ _ HAR3m HREP4 Hkeep4) as HREP5.
destruct (lrfb_rep_acall ly3 S3 _ R REC_LV2_REFUSALS_FORGET [lrfb_x uri] _ HREP5) as (P & HCALL).
pose proof (lrfb_aro_kept _ _ O ly S W mem md _ ly3 S3 W3 (ms_mem ms4) _ _ HJ3 HAR HO HROD) as HROD4.
pose proof (cmd_ro_ok_of_aro ly3 S3 W3 (ms_mem ms4) _ (proj1 HJ3) HROD4) as HROOK4.
assert (HNEV4 : st_nev S3 + EV_MIX_CALL <= EV_MAX).
{ pose proof HJ3 as (_ & _ & _ & _ & _ & _ & Hn4 & _). unfold EV_MIX_CALL, EV_LV2_REFUSALS_FORGET in *. lia. }
assert (Hs0m : s0Z (ms_regs ms4) = rec_slot R).
{ unfold s0Z. rewrite R8, OLD3 by lia. rewrite E52, Ha02. apply unsigned_lit_small. lia. }
pmkst HS. rewrite lrfb_sig_mix_call.
eapply SRr_bind.
{ eapply (cl_callS_wide B LAWS W3 (ms_regs ms4) (ms_mem ms4) _ LV2_REFUSALS_FORGET_STK (spZ regs) (lrfb_FP O) ly S W mem md []
    ly3 S3 _ (0 + EV_RECORD R + EV_ARG_S) MIX_CALL_STK [] EV_MIX_CALL (-32) (getr (ms_regs ms4) 1) [] _ HJ3).
  - exact Esp4.
  - reflexivity.
  - lia.
  - rewrite HMSv. lia.
  - rewrite HMSv, HSTKv. lia.
  - rewrite R3, OLD3, OLD2 by lia. rewrite (EE 3%nat 3%bv eq_refl). exact Hgp.
  - rewrite R4, OLD3, OLD2 by lia. rewrite (EE 4%nat 4%bv eq_refl). exact Htp.
  - reflexivity.
  - rewrite R1. apply ret_ok_codeptr_v; [lia | reflexivity].
  - rewrite R1, unsigned_lit_small by lia. lia.
  - apply achain_low. rewrite Hs0m. lia.
  - intros HPRE4. eapply SRr_mono.
    { apply (TMIX_CALL fx ly3 S3 W3 (ms_regs ms4) (ms_mem ms4) _ (r_state R) (rec_slot R)
        (REC_LV2_REFUSALS_FORGET, [lrfb_x uri]) P (afn_pre_na_of SEGS B _ _ _ _ _ _ _ _ HPRE4) HROD4).
      - rewrite R10, OLD3, OLD2 by lia. exact E32.
      - exact Hh.
      - rewrite R11, OLD3 by lia. rewrite E52. exact Ha02.
      - apply lrfb_slot_cases.
      - exact HCALL.
      - exact HROOK4.
      - exact HNEV4. }
    intros W4 c4 _ Hc4. exact Hc4.
  - intros a Ha. destruct (inFP_nil a Ha).
  - intros ? ? ? ? ? ? _ a Ha. destruct (inFP_nil a Ha). }
cbv beta. intros W4 c4 Hwle4 (ly4 & S4 & regs4 & mem4 & md4 & -> & HJ4 & HJc4 & HP4 & (Hm10 & Hperm4 & -> & ->)).
cbn [fst snd] in Hm10.
rewrite R1.
jafter_call_keep_pi HS 80%nat regs4 (mrestrict (w_H W4) mem4) HP4 [1]%nat HS4.
match type of HS4 with ?t -> _ => assert (HRK : t); [|specialize (HS4 HRK); clear HRK] end.
{ cbn [ms_mem restrict]. repeat apply Forall_cons; [| apply Forall_nil].
  eapply (lrfb_region_kept_hi2 SEGS E3 (w_H W3) (w_H W4) (ms_mem ms4) mem4 2 (spZ regs)); [exact Usp3 | |].
  - intros a Ha. pose proof HJc4 as (_ & _ & _ & _ & _ & _ & _ & _ & K9 & _).
    apply K9; [lia | rewrite HMSv; lia | apply inFP_nil].
  - intros a Ha. pose proof HJ4 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HP14 & _).
    apply HP14. rewrite HSTKv. lia. }
clear HS R10 R11 R2 R3 R4 R1 R8.
remember (havoc E3 80 (map (getr regs4) CLOB)) as E4 eqn:HE4 in HS4.
assert (HEI4 : img_env VAL A_LIM E4) by (rewrite HE4; apply img_env_havoc; [exact HEI3 | cbv; lia]).
assert (OLD4 : forall n, (n < 80)%nat -> ew E4 n = ew E3 n) by (intros n' Hn'; rewrite HE4; apply YN3v.ew_havoc_old; exact Hn').
assert (HAE4 : env_agree 32 (Ereg regs (lrfb_extra (r_state R) (lrfb_s pu))) E4)
  by (rewrite HE4; apply env_agree_havoc_ge; [cbv; lia | exact HAE3]).
assert (E84 : ew E4 84 = getr regs4 10) by (rewrite HE4; reflexivity).
clear HE4.
assert (Usp4 : bv_unsigned (ew E4 2) = spZ regs) by (rewrite OLD4 by lia; exact Usp3).
assert (UHS4 : bv_unsigned (ew E4 L_HSTATE) = 0x5e3d8c)
  by (rewrite (HEI4 L_HSTATE ltac:(unfold L_HSTATE, A_HI, A_TEXT, A_LIM; lia)); exact lrfb_hstate_val).
(* the region of the store at 0x8cd9c: g_rec.state, through the auipc atom A_HI 207 *)
pose proof (st_ok_pi_add_region E4 _ _ lrfb_store_region HS4 eq_refl) as HS.
match type of HS with ?t -> _ => assert (HRK : t); [|specialize (HS HRK); clear HRK] end.
{ unfold region_ok, lrfb_store_region.
  cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val ms_mem mkst].
  rewrite UHS4. split; [lia|]. split; [lia|]. split; [|constructor].
  intros o Ho. apply PROG_WRITABLE. exists (A_G_REC, A_G_REC + 960). split; [left; reflexivity|].
  cbn [fst snd]. unfold A_G_REC. lia. }
match type of HS with ?t -> _ => assert (HRK : t); [|specialize (HS HRK); clear HRK] end.
{ cbn [all_disjoint ss_mem]. split; [|exact I]. unfold extent_disjoint, lrfb_store_region.
  cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite UHS4, Usp4. lia. }
lazymatch type of HS with st_ok_pi _ _ _ ?s _ => let v := eval vm_compute in s in change s with v in HS end.
clear HS4. rewrite <- restrict_mkst_fx in HS.
(* 0x8cd9c .. 0x8cdb0: g_rec.state := the digest, the callee-saved registers back, return *)
paj_run_shc RUNP RUNC HS HJ4.
{ lazymatch goal with |- awr_ok _ _ ?Ex ?rs ?stk ?spx ?fp ?b0 ?bc ?fr ?lyx ?own =>
  let rs' := eval vm_compute in rs in change (awr_ok SEGS B Ex rs' stk spx fp b0 bc fr lyx own) end.
  eapply lrfb_awr_cons_hstate; [reflexivity | exact HEI4 | cbn; lia | cbn; lia |].
  eapply awr_ok_cons_stack; [reflexivity | exact Usp4 | cbn [YP09.r_wlo]; lia | cbn [YP09.r_whi]; lia | apply awr_ok_nil]. }
clear HF HG. rename HFr into HFr5. rename ms into ms5.
eapply (RET W4 _ _ _ _ _ HS eq_refl ltac:(vm_compute; reflexivity)).
intros matF.
prreg HS (1%bv : bv 5) Rf1.
pose proof (st_ok_pi_region_nth E4 _ _ 0 _ HS eq_refl) as HRf. cbn [ms_mem restrict] in HRf.
pose proof (field_of_region_any E4 _ L_HSTATE 0x5e3d8c _ _ _ _ _ (-1820) 8 (SOff 84 0) HRf UHS4 ltac:(cbn; tauto) ltac:(cbn; lia))
  as Fst.
assert (HhF : 0 <= mixcall (r_state R) REC_LV2_REFUSALS_FORGET [lrfb_x uri] < 2 ^ 64) by (apply mixcall_range; exact Hh).
assert (D84 : bv_unsigned (sv_denot E4 (SOff 84 0)) mod 2 ^ (8 * Z.of_N 8) = mixcall (r_state R) REC_LV2_REFUSALS_FORGET [lrfb_x uri]).
{ cbn [sv_denot]. rewrite E84, Hm10, Z.add_0_r. unfold w64. rewrite Z_to_bv_bv_unsigned, unsigned_lit_small by lia.
  apply Z.mod_small. change (8 * Z.of_N 8) with 64. exact HhF. }
rewrite D84 in Fst. replace (0x5e3d8c + -1820) with (A_G_REC + OFF_STATE) in Fst by (unfold A_G_REC, OFF_STATE; lia).
(* what the last run, mix_call and the run before it keep *)
assert (UHS4' : bv_unsigned (ew E4 607) = 0x5e3d8c) by exact UHS4.
assert (K5 : forall a, 0 <= a < alloc_ceiling -> ~ (A_G_REC + OFF_STATE <= a < A_G_REC + OFF_STATE + 8) ->
  rdW W4 (ms_mem ms5) a = rdW W4 mem4 a).
{ intros a Ha Hns. apply (recb_run_keeps_m (PI := PI) E4 _ (w_H W4) mem4 (ms_mem ms5) a HFr5); [lia|].
  intros (r & Hr' & Hw). vm_compute in Hr'.
  repeat (destruct Hr' as [Hr' | Hr']; [subst r; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hw; rewrite ?Usp4, ?UHS4' in Hw;
    unfold A_G_REC, OFF_STATE in Hns; lia|]).
  destruct Hr'. }
assert (KPG : forall a, Exists (in_zr a) TFIB_PROG_STATIC -> ~ (A_G_REC + OFF_STATE <= a < A_G_REC + OFF_STATE + 8) ->
  rdW W4 (ms_mem ms5) a = rdW W3 mem3 a).
{ intros a HP Hns. pose proof (lrfb_PG_img a HP) as HIa.
  rewrite (K5 a ltac:(lia) Hns).
  rewrite (lrfb_callee_keeps_PG _ _ [] _ _ _ _ _ _ _ _ _ _ _ _ a HJc4); [| intros (r & Hr & _); destruct Hr | apply inFP_nil | exact HP].
  apply Hkeep4. lia. }
assert (KBL : forall pn i, In pn (ablocks B ly3 S3) -> 0 <= i < snd pn ->
  rdW W4 (ms_mem ms5) (fst pn + i) = rdW W3 mem3 (fst pn + i)).
{ intros [q k] i Hin Hi. cbn [fst snd] in Hi |- *.
  destruct (al_blocks _ _ LAWS _ _ _ _ _ q k (proj1 HJc4) Hin) as (_ & Hq4 & Hqc & _ & _ & _ & Hk).
  pose proof (req_size_pos k ltac:(lia)) as [_ Hrk].
  pose proof (blk_off_imgP B ly3 S3 W4 mem4 md4 q k (proj1 HJc4) Hin) as Hoff. unfold off_img in Hoff.
  rewrite (K5 (q + i) ltac:(lia) ltac:(unfold A_G_REC, OFF_STATE; lia)).
  pose proof HJc4 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & K10 & _).
  rewrite (K10 q k i Hin ltac:(eapply Permutation_in; [apply Permutation_sym; exact Hperm4 | exact Hin]) ltac:(lia) (inFP_nil _)).
  apply Hkeep4. lia. }
assert (HREP6 : rec_repA B ly3 S3 (rdW W4 (ms_mem ms5)) (lv2_refusals_forget_m R uri) ((p, n) :: O1)).
{ rewrite lrfb_m_eq.
  apply (lrfb_rep_set ly3 S3 (rdW W3 mem3) _ _ _ _ HREP4).
  - intros a Ha Hns. apply KPG; [apply lrfb_in_PG_grec; exact Ha | exact Hns].
  - intros a Ha. apply KPG; [apply lrfb_in_PG_spill; exact Ha | unfold A_G_REC, OFF_STATE, A_REC_SPILL, SC_SIZE in *; lia].
  - intros pn i Hpn Hi. apply KBL; [exact (lrfb_rep_O_in ly3 S3 _ _ _ HREP4 pn Hpn) | exact Hi].
  - exact (aval_mem_view SEGS (w_H W4) (ms_mem ms5) _ _ _ Fst).
  - exact HhF. }
assert (Hra1' : getr (ms_regs ms5) 1 = getr regs 1)
  by (rewrite Rf1, OLD4, OLD3, OLD2 by lia; exact (EE 1%nat 1%bv eq_refl)).
pose proof Hra as Hra'. unfold YK0s.ret_ok in Hra'.
pose proof (recb_ablocks_nodup_m (PI := PI) B ly S W mem md HAR) as ND0.
assert (NDP : List.NoDup (ablocks B ly2 S2 ++ F)) by exact (Permutation_NoDup Hperm2 ND0).
unfold apost_base. eexists ly3, S3, (ms_regs ms5), (ms_mem ms5), _.
split; [rewrite Hra1', Hra'; reflexivity|].
split; [apply (ajournal_mono_k SEGS B) with (k := 0 + EV_RECORD R + EV_ARG_S + EV_MIX_CALL);
  [apply (ajournal_materialize SEGS B LAWS pa_segs_low); exact HJ4 | unfold EV_LV2_REFUSALS_FORGET, EV_MIX_CALL; lia]|].
split; [exact (aregs_preserved_of_st_ok SEGS (w_H W4) E4 _ ms5 regs (lrfb_extra (r_state R) (lrfb_s pu)) HS HAE4 ltac:(vm_compute; reflexivity))|].
exists ((p, n) :: O1).
split; [exact HREP6|].
split.
{ intros pn [<- | Hpn].
  - destruct (in_dec recb_pair_dec (p, n) (ablocks B ly S)) as [Hin | Hnin]; [left | right; exact Hnin].
    apply (Permutation_in _ Hperm2) in Hin. apply in_app_or in Hin as [Hin | Hin]; [|exact (HFO _ Hin)].
    exfalso. pose proof (proj1 (Forall_forall _ _) Hfresh3 (p, n) Hin) as Hap. unfold iv_apart in Hap. cbn [fst snd] in Hap. lia.
  - left. exact (proj1 (proj1 (HO1 pn) Hpn)). }
split.
{ intros pn Hin HnO. apply (Permutation_in _ Hperm2) in Hin. apply in_app_or in Hin as [Hin | Hin]; [|exfalso; exact (HnO (HFO _ Hin))].
  eapply Permutation_in; [apply Permutation_sym; exact Hperm3 | right; exact Hin]. }
split.
{ intros pn Hin. apply (Permutation_in _ Hperm3) in Hin. destruct Hin as [<- | Hin]; [right; left; reflexivity|].
  assert (Hin0 : In pn (ablocks B ly S)) by (eapply Permutation_in; [apply Permutation_sym; exact Hperm2 | apply in_or_app; left; exact Hin]).
  destruct (in_dec recb_pair_dec pn O) as [HinO | HnO]; [right; right | left; split; [exact Hin0 | exact HnO]].
  apply (proj2 (HO1 pn)). split; [exact HinO|]. intros HF. exact (list_nodup_app_disj _ _ pn NDP Hin HF). }
split.
{ unfold LIVE_LV2_REFUSALS_FORGET. unfold lrfb_x in HBB3. lia. }
apply (mo_le_mono MT MTL S S3 (XM_RECORD MT R + XM_ARG_S MT (Some (lrfb_x uri)))).
- exact (mo_le_trans MT MTL _ _ _ _ _ MLE2 MLE3).
- unfold XM_LV2_REFUSALS_FORGET, lrfb_x. lia.
Qed.
End e.
End f.
End d.
