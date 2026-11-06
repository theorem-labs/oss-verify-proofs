(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* fs program part, READER lane (a Theorem Labs lane): the SEGMENTS of parse_items' member path - the walk's
   fixed data, the start-state builders, and segment E measured. Every segment starts at a state the walk builds
   (FSW_parse_items_kit.v) and runs, with the engine, straight to the next call stop or to the `ret`, raising NO
   obligation. The member-loop segments are measured in the step files on their start states with narrowed write
   windows (so that frame_of keeps every byte a segment does not write):
     E    0x84ad0 arm (in->p + 1 < in->end)  -> grow #1 entry 0x83a48, ra 0x84b6c   pi_run_e pr k (here)
     S1f  grow #1 resume 0x84b6c              -> parse_string 0x850b8, ra 0x84c50   FSW_parse_items_stG.piG_run_s1f
     S1   grow #2 resume 0x84e64              -> parse_string 0x850b8, ra 0x84c50   FSW_parse_items_stG.piG_run_s1 pr k
     S2   parse_string resume 0x84c50         -> __asan_memset 0x521bc, ra 0x84d7c  FSW_parse_items_stP.pip_run_s2
     S3   __asan_memset resume 0x84d7c        -> parse_value 0x82f9c, ra 0x84d9c    FSW_parse_items_stM.pim_run_s3
     S4c  parse_value resume 0x84d9c, `,`     -> grow #2 entry 0x83a48, ra 0x84e64   FSW_parse_items_stVc.pvc_run
     S4e  parse_value resume 0x84d9c, `}`     -> `ret` 0x84f10 (jalr to the entry ra) FSW_parse_items_stVe.pve_run pr k
   THE WHITE-SPACE LOOPS need no induction: parse_items_spec is level-indexed with k <= 1, so the white space every loop
   meets is a concrete byte list per (pr, k) (WriterValue.wind pr (k + 1) after `{` and after `,`, wind pr k before
   `}`, nothing before `:`). The walk gives those bytes, and the byte after them, as a read-only literal window at the
   cursor atom (FSW_parse_items_kit.pik_treg) and adds the loop's back-edge conditions `cursor + j <> in->end` and the
   `in->p < in->end` guards as facts: the engine decides a branch from f_conds (YP0e.decide_cond2), so each loop runs
   through. The writer text gives every one of those conditions (FSW_parse_items_mdl.v).
   THE SLOTS keys + 8 n (the key store at 0x84c94) and kids + 56 n (the kid, a0 of the memset and a1 of parse_value)
   are extra env atoms xatom 22 / xatom 23 with an alias fact each: the engine's ALU results go through
   YP0e.aliased2, so the computed address is the slot atom itself, and the key store lands in an 8-byte window there.
   ATOMS at every resume (a Theorem Labs lane's call steps, FSW_parse_items_grow.v / _calls.v): atom 8 = s0 = q, atom 20 = s4 = v,
   atom 32 = the shadow base, xatom 0 / 1 / 2 = in->p / in->end / in->depth at the resume, xatom 3 .. 15 = the entry ra,
   s0 .. s11 (pi_saved order, the frame slots 136 .. 40), xatom 16 .. 19 = kids / keys / n / cap, xatom 20 / 21 = the key
   block and its length (parse_string's resume only), xatom 22 / 23 = the slots.
   MEASURED on the pinned fs.asan with the engine (vm_compute); the scouting probes and their outputs are
   a Theorem Labs lane's p1.b.v .. p3.b.v (+ .out, header hdr.v), 2026-10-29 08:4xZ. Rule 24: no
   function is proved in this file (parse_items' lookup: the CONFIRM verdict, lookup/confirm-resume.md). *)
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.omx_clap_core.fuzz_state.images Require Import Asan.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YN3v YI04 YI09 YI08 YI00 YI0n.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YI16 YK06 YM05 YG0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.A Require Import
AB1v AB1w FSupoison FSupoisonU FSH_YC20 FSH_Gen FSH_Base FSH_Rt FSW_K FSW_ret
FSW_parse_items_tbl FSW_parse_items FSW_parse_items_grow FSW_parse_items_calls FSW_parse_items_kit.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Prog Require WriterValue.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.
(* SINK GUARD (S0): a SUCCESS here (the build errors naming this line) means a WRONG sink instance resolved. *)
Fail Definition probe_SK : Reusable.YI16.sink_head := _.
Fail Definition probe_SH : Reusable.YI14.sink_syms := _.

(* ================= the walk's fixed data ================= *)
(* the thirteen registers the prologue saves, in xatom order 3 .. 15: ra, s0, s1, s2 .. s11 (frame slots 136 .. 40) *)
Definition pi_saved : list (bv 5) := [1; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%bv.
Definition pi_cs0 : list YP09.chunk :=
  map (fun j => YP09.mkChunk (136 - 8 * Z.of_nat j) (CVal 8 (SOff (xatom (3 + j)) 0))) (seq 0 13).
(* the ASan shadow address of atom b + c, in the engine's form *)
Definition pi_shv (b : nat) (c : Z) : sv := SAlu ALU_ADD (SAlu ALU_SRL (SOff b c) (SLit 3)) (SOff 32 0).
(* the frame after the member-loop set-up 0x84b70 .. 0x84ba8: q + 8, shadow (q + 16), shadow (v + 24), v + 32 *)
Definition pi_csL : list YP09.chunk :=
  [YP09.mkChunk 8 (CVal 8 (SOff 8 8)); YP09.mkChunk 16 (CVal 8 (pi_shv 8 16)); YP09.mkChunk 24 (CVal 8 (pi_shv 20 24));
   YP09.mkChunk 32 (CVal 8 (SOff 20 32))] ++ pi_cs0.
(* the callee-saved registers before the set-up (grow #1) and in the member loop (every later call) *)
Definition pi_R0 : list (bv 5 * sv) :=
  [(9%bv, SOff 8 16); (19%bv, SLit 1); (21%bv, pi_shv 8 16); (22%bv, SOff 8 8); (23%bv, pi_shv 8 8);
   (26%bv, SOff 32 0); (27%bv, pi_shv 8 0)].
Definition pi_RL : list (bv 5 * sv) :=
  [(9%bv, SOff 8 16); (18%bv, pi_shv 20 40); (19%bv, SLit 1); (21%bv, SLit 32); (22%bv, SOff 20 40);
   (23%bv, pi_shv 8 8); (24%bv, SOff 20 24); (25%bv, SLit 4294977024); (26%bv, SOff 32 0); (27%bv, pi_shv 8 0)].
(* the white space of a writer indent, as bytes *)
Definition pi_wsb (pr : bool) (d : Z) : list Z := concat (WriterValue.wind pr d).
(* a white-space loop's conditions: n white-space bytes at the cursor xatom 0 + o, then a stop byte, all before
   in->end (xatom 1) *)
Definition pi_wsc (n : nat) (o : Z) : list acond :=
  map (fun j => mkAC BC_NE (SOff (xatom 0) (o + 1 + Z.of_nat j)) (SOff (xatom 1) 0)) (seq 0 n)
  ++ [mkAC BC_LTU (SOff (xatom 0) (o + Z.of_nat n)) (SOff (xatom 1) 0); mkAC BC_LTU (SOff (xatom 0) o) (SOff (xatom 1) 0)].
(* the slots: keys + 8 n at xatom 22 (an 8-byte writable window), kids + 56 n at xatom 23 *)
Definition pi_kaR : YP09.region := YP09.mkRegion (Some (xatom 22)) 0 8 0 8 [].
Definition pi_al_ka : sv * sv :=
  (SAlu ALU_ADD (SOff (xatom 17) 0) (SAlu ALU_SLL (SOff (xatom 18) 0) (SLit 3)), SOff (xatom 22) 0).
Definition pi_al_vk : sv * sv :=
  (SAlu ALU_ADD (SOff (xatom 16) 0) (SMd M_MUL (SOff (xatom 18) 0) (SLit 56)), SOff (xatom 23) 0).
Definition pi_gf_ka : list (nat * afact) := [(xatom 22, mkAF 4096 (2 ^ 47 - 2 ^ 23) 3)].
Definition pi_gf_vk : list (nat * afact) := [(xatom 23, mkAF 4096 (2 ^ 47 - 2 ^ 23) 3)].
(* the shadow entries of a member-loop run: q (atom 8) and v (atom 20) *)
Definition pi_SHm : list shent := [mkSHE 8 0 24; mkSHE 20 0 56].
Definition pi_tok_run (SH : list shent) (s : sstate) : shst * trun_status :=
  sym_runN_tok tfibsegs pitems_tbl (run_K 0 fs_Bx SH s) fs_Bx fs_Bspan SH FUEL s.
(* a register list holds in a state *)
Definition pi_regs_are (s : sstate) (l : list (bv 5 * sv)) : bool :=
  forallb (fun q => sv_eqb (sr_get (ss_regs s) (fst q)) (snd q)) l.

(* ================= E: from the 0x84ad0 arm to grow #1 ================= *)
Definition pi_ss_e (pr : bool) (k : nat) : sstate :=
  let ws := pi_wsb pr (Z.of_nat k + 1) in
  pik_addf (pik_addr pi_ss_ws0 [pik_treg (xatom 0) 1 (ws ++ [34])]) [] (pi_wsc (length ws) 1) [].
Definition pi_SH_e (pr : bool) (k : nat) : list shent :=
  mkSHE (xatom 0) 1 (2 + Z.of_nat (length (pi_wsb pr (Z.of_nat k + 1)))) :: pi_SH.
Definition pi_st_e (pr : bool) (k : nat) : shst := fst (pi_tok_run (pi_SH_e pr k) (pi_ss_e pr k)).
Lemma pi_static_e : forall pr k, (k <= 1)%nat ->
  sh_static_ok (run_K 0 fs_Bx (pi_SH_e pr k) (pi_ss_e pr k)) fs_Bx fs_Bspan (pi_SH_e pr k)
    (ss_facts (pi_ss_e pr k)) (ss_mem (pi_ss_e pr k)) = true.
Proof. intros [|] [|[|k]] Hk; try lia; vm_compute; reflexivity. Qed.
Lemma pi_run_e : forall pr k, (k <= 1)%nat ->
  pi_tok_run (pi_SH_e pr k) (pi_ss_e pr k) = (pi_st_e pr k, TS_stopped SR_fetch).
Proof. intros [|] [|[|k]] Hk; try lia; vm_compute; reflexivity. Qed.
(* at grow #1: pc A_grow, ra 0x84b6c, a0 = v; the callee-saved registers; in->p past the white space; no obligation *)
Lemma pi_fin_e : forall pr k, (k <= 1)%nat ->
  let s := sh_ss (pi_st_e pr k) in
  ss_pc s = A_grow /\ sh_obls (pi_st_e pr k) = [] /\ ss_resv s = None /\
  sh_j (pi_st_e pr k) = (4 + 2 * length (pi_wsb pr (Z.of_nat k + 1)))%nat /\
  pi_regs_are s
    [(1%bv, SLit 0x84b6c); (2%bv, SOff 2 (-144)); (3%bv, SOff 3 0); (4%bv, SOff 4 0); (8%bv, SOff 10 0);
     (10%bv, SOff 11 0); (20%bv, SOff 11 0);
     (9%bv, SOff 10 16); (19%bv, SOff 12 0); (21%bv, pi_shv 10 16); (22%bv, SOff 10 8); (23%bv, pi_shv 10 8);
     (26%bv, SOff 32 0); (27%bv, pi_shv 10 0)] = true /\
  nth_error (ss_mem s) 1 =
    Some (YP09.mkRegion (Some 2%nat) (-144) 0 (-144) 0
      (rev (map (fun j => YP09.mkChunk (-8 - 8 * Z.of_nat j)
                            (CVal 8 (SOff (Z.to_nat (bv_unsigned (nth j pi_saved 0%bv))) 0))) (seq 0 13)))) /\
  nth_error (ss_mem s) 4 =
    Some (YP09.mkRegion (Some 10%nat) 0 24 0 24
      [YP09.mkChunk 0 (CVal 8 (SOff (xatom 0) (1 + Z.of_nat (length (pi_wsb pr (Z.of_nat k + 1))))));
       YP09.mkChunk 16 (CVal 4 (SOff (xatom 2) 1)); YP09.mkChunk 8 (CVal 8 (SOff (xatom 1) 0))]) /\
  nth_error (ss_mem s) 5 = Some pi_v_region6.
Proof. intros [|] [|[|k]] Hk; try lia; vm_compute; repeat split; reflexivity. Qed.

(* ================= the member-loop start states (builders) =================
   Each is the kit's resume state of a call with the callee-saved registers restated, the text window and the
   white-space conditions added. The step files narrow the write windows of these states with pik_st_ok_setm (v's to
   [0,0) or [40,48), and all of them for S3), so that frame_of keeps every byte the segment does not write, and measure
   the narrowed states themselves: FSW_parse_items_stG.v (S1f, S1), _stP.v (S2), _stM.v (S3), _stVc.v (S4c),
   _stVe.v (S4e). *)
(* S1f: grow #1 resume to parse_string *)
Definition pi_ss_s1f : sstate :=
  pik_addf (pik_addr (pik_setr (fss_retT 0x84b6c 144 pi_cs0 pig_rs pig_gf) ((10%bv, SLit 0) :: pi_R0))
    [pik_treg (xatom 0) 0 [34]]) [] (pi_wsc 0 0) [].
(* S1: grow #2 resume to parse_string *)
Definition pi_ss_s1 (pr : bool) (k : nat) : sstate :=
  let ws := pi_wsb pr (Z.of_nat k + 1) in
  pik_addf (pik_addr (pik_setr (fss_retT 0x84e64 144 pi_csL pig_rs pig_gf) ((10%bv, SLit 0) :: pi_RL))
    [pik_treg (xatom 0) 0 (ws ++ [34])]) [] (pi_wsc (length ws) 0) [].
(* the parse_string call, from either resume: pc A_parse_string, ra 0x84c50, a0 = q, the member loop's registers, the
   frame pi_csL; in->p at the opening quote *)
Definition pi_regs_ps : list (bv 5 * sv) :=
  [(1%bv, SLit 0x84c50); (2%bv, SOff 2 0); (3%bv, SOff 3 0); (4%bv, SOff 4 0); (8%bv, SOff 8 0); (10%bv, SOff 8 0);
   (20%bv, SOff 20 0)] ++ pi_RL.
(* S2: parse_string resume to the memset (the key stored at keys[n], `:`) *)
Definition pi_ss_s2 : sstate :=
  pik_addf (pik_addr (pik_setr (fss_retT 0x84c50 144 pi_csL pig_rs pic_gf_ps) ((10%bv, SOff (xatom 20) 0) :: pi_RL))
    [pik_treg (xatom 0) 0 [58]; pi_kaR]) (pi_gf_ka ++ pi_gf_vk) (pi_wsc 0 0) [pi_al_ka; pi_al_vk].
Definition pi_SH_s2 : list shent := mkSHE (xatom 0) 0 1 :: mkSHE (xatom 22) 0 8 :: pi_SHm.
(* S3: memset resume to parse_value *)
Definition pi_ss_s3 : sstate :=
  pik_addf (pik_setr (fss_retT 0x84d7c 144 pi_csL pig_rs pic_gf) pi_RL) pi_gf_vk [] [pi_al_vk].
(* S4c / S4e: parse_value resume, `,` (to grow #2) or `}` (to the ret) *)
Definition pi_ss_s4c : sstate :=
  pik_addf (pik_addr (pik_setr (fss_retT 0x84d9c 144 pi_csL pig_rs pic_gf) ((10%bv, SLit 0) :: pi_RL))
    [pik_treg (xatom 0) 0 [44]]) [] (pi_wsc 0 0) [].
Definition pi_SH_s4c : list shent := mkSHE (xatom 0) 0 1 :: pi_SHm.
Definition pi_ss_s4e (pr : bool) (k : nat) : sstate :=
  let ws := pi_wsb pr (Z.of_nat k) in
  pik_addf (pik_addr (pik_setr (fss_retT 0x84d9c 144 pi_csL pig_rs pic_gf) ((10%bv, SLit 0) :: pi_RL))
    [pik_treg (xatom 0) 0 (ws ++ [125])]) [] (pi_wsc (length ws) 0) [].
Definition pi_SH_s4e (pr : bool) (k : nat) : list shent :=
  mkSHE (xatom 0) 0 (1 + Z.of_nat (length (pi_wsb pr (Z.of_nat k)))) :: pi_SHm.
(* at the ret: a0 = 0, sp = the entry sp, s0 .. s11 the entry values (xatom 4 .. 15), the entry ra (xatom 3) *)
Definition pi_regs_ret : list (bv 5 * sv) :=
  [(10%bv, SLit 0); (2%bv, SOff 2 144); (8%bv, SOff (xatom 4) 0); (9%bv, SOff (xatom 5) 0);
   (18%bv, SOff (xatom 6) 0); (19%bv, SOff (xatom 7) 0); (20%bv, SOff (xatom 8) 0); (21%bv, SOff (xatom 9) 0);
   (22%bv, SOff (xatom 10) 0); (23%bv, SOff (xatom 11) 0); (24%bv, SOff (xatom 12) 0); (25%bv, SOff (xatom 13) 0);
   (26%bv, SOff (xatom 14) 0); (27%bv, SOff (xatom 15) 0); (1%bv, SOff (xatom 3) 0)].

(* the frame regions of the resume states are well formed (a premise of every call step) *)
Lemma pi_wf_csL : regions_wf [fstk_ret 144 pi_csL] = true.
Proof. vm_compute. reflexivity. Qed.
Lemma pi_wf_cs0_g : regions_wf (fsT_ret_regions 144 pi_cs0 pig_rs) = true.
Proof. vm_compute. reflexivity. Qed.
Lemma pi_wf_csL_g : regions_wf (fsT_ret_regions 144 pi_csL pig_rs) = true.
Proof. vm_compute. reflexivity. Qed.
