(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: from proofs/plugin-hostd/fuzz_reply/lib/A/RepVsnD.v (commit eb934de95d13, blob 77da4831bdd3) onto omx-clap-core/fuzz_preset's asan image (unstripped fuzz_preset.asan, sha256 bff8519bbe3e; pin 1be0f53d96cb), from reply A d751b179ea49 (pin 42c58610e125); module paths changed; 5 image numerals moved by port_addr_check 3d2eee813cce MAPS predictions and the twins' symbol + offset map (0 model labels and sizes kept); no other numeral changed; comments removed (the source file keeps them); the two VSNPrintf conversion-table WORDS are offsets from the table base (A' 0x20c64, CfImgA.v:81), not code addresses: 0x20c64 + 0x46e08 = 0x67a6c = VSNPrintf+0x1fc and 0x20c64 + 0x46de0 = 0x67a44 = VSNPrintf+0x1d4; both read from the A' twin at 0x20cd0 / 0x20cd8. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool String Ascii.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s YO0d.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YP0j.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YN3v YI04.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK04 YA0i YA0n YA0o YA0p YA0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG00 YG0f.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import AB1v AB1q AF0m AF0x.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import RepIFcf.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.

Definition vrom (a : Z) (bs : list Z) : YP09.region :=
  YP09.mkRegion None a (a + Z.of_nat (length bs)) 0 0
    (map (fun i => YP09.mkChunk (a + Z.of_nat i) (CVal 1 (SLit (nth i bs 0)))) (seq 0 (length bs))).
Definition vlit4 (a v : Z) : YP09.region := YP09.mkRegion None a (a + 4) 0 0 [YP09.mkChunk a (CVal 4 (SLit v))].
Definition TOOL_BYTES : list Z := str_z "AddressSanitizer" ++ [0].
Definition JT_S : Z := 0x20cd0.
Definition JT_U : Z := 0x20cd8.
Definition ROM_JT : smem := [vlit4 JT_S 0x46e08; vlit4 JT_U 0x46de0].
Definition ROM1 : smem := vrom FMT_OOM1 FMT1_BYTES :: vrom A_TOOLNAME TOOL_BYTES :: ROM_JT.
Definition ROM2 : smem := vrom FMT_OOM2 FMT2_BYTES :: ROM_JT.

Definition R_S : YP09.region := YP09.mkRegion (Some 2%nat) (- VSN_STK) 0 (- VSN_STK) 0 [].

Definition R_B (n : Z) : YP09.region := YP09.mkRegion (Some 10%nat) 0 n 0 n [].

Definition R_VA (vs : list Z) : YP09.region :=
  YP09.mkRegion (Some 13%nat) 0 (8 * Z.of_nat (length vs)) 0 0
    (map (fun i => YP09.mkChunk (8 * Z.of_nat i) (CVal 8 (SLit (nth i vs 0)))) (seq 0 (length vs))).

Definition MS_AL : sv := SAlu ALU_AND (SAlu ALU_OR (SLit 240) (SOff 2 (-456))) (SLit 15).
Definition VFACTS : facts := mkFacts
  [ (2%nat, mkAF (kHighMemBeg + VSN_STK) kHighMemEnd 4);
    (10%nat, mkAF kHighMemBeg kHighMemEnd 0); (13%nat, mkAF kHighMemBeg kHighMemEnd 0) ] [] [(MS_AL, SLit 8)].
Definition VREGS (fmt : Z) : list sv := sr_set (sr_set sr_atoms 11%bv (SLit 400)) 12%bv (SLit fmt).
Definition vmem (n : Z) (vs : list Z) (rom : smem) : smem := R_S :: R_B n :: R_VA vs :: rom.
Definition vseed (fmt n : Z) (vs : list Z) (rom : smem) : sstate := mkSS A_VSNPRINTF (VREGS fmt) (vmem n vs rom) None VFACTS.

Definition A_VSN_RET : Z := 0x67d00.
Definition zdisjb (a b : Z * Z) : bool := (snd a <=? fst b) || (snd b <=? fst a).
Fixpoint zpw_disjb (l : list (Z * Z)) : bool :=
  match l with [] => true | a :: l' => forallb (zdisjb a) l' && zpw_disjb l' end.

Definition rom_ok (rom : smem) : bool :=
  forallb (fun r => YP09.obase_eqb (YP09.r_base r) None && (TFIB_IMG_LO <=? YP09.r_lo r) &&
    (YP09.r_hi r <=? TFIB_IMG_END) && (YP09.r_whi r <=? YP09.r_wlo r)) rom &&
  zpw_disjb (map (fun r => (YP09.r_lo r, YP09.r_hi r)) rom).
Definition chunk_has (cs : list YP09.chunk) (off v : Z) : bool :=
  existsb (fun c => (YP09.c_off c =? off) &&
    match YP09.c_val c with CVal w (SLit x) => (w =? 1)%N && (x =? v) && (0 <=? v) && (v <? 256) | _ => false end) cs.
Fixpoint wins_eqb (l l' : list (option nat * Z * Z)) : bool :=
  match l, l' with
  | [], [] => true
  | t :: l1, u :: l1' => win_eqb t u && wins_eqb l1 l1'
  | _, _ => false
  end.
Definition vfin_ok (seed ssF : sstate) (out : list Z) : bool :=
  (ss_pc ssF =? A_VSN_RET) && match ss_resv ssF with None => true | Some _ => false end &&
  forallb (fun r : reg => sv_eqb (sr_get (ss_regs ssF) r) (SOff (Z.to_nat (bv_unsigned r)) 0)) CALLEE_SAVED &&
  sv_eqb (sr_get (ss_regs ssF) 1%bv) (SOff 1 0) &&
  sv_eqb (sr_get (ss_regs ssF) 10%bv) (SLit (Z.of_nat (length out))) &&
  wins_eqb (windows (ss_mem ssF)) (windows (ss_mem seed)) &&
  match nth_error (ss_mem ssF) 1 with
  | Some r => YP09.obase_eqb (YP09.r_base r) (Some 10%nat) &&
      forallb (fun i => chunk_has (YP09.r_chunks r) (Z.of_nat i) (nth i (out ++ [0]) 0)) (seq 0 (S (length out)))
  | None => false
  end.
Definition vrun (seed : sstate) : sstate * run_status := sym_run_toN_sh tfibsegs tfibtbl_rtD YP03.FUEL A_VSN_RET seed.
Definition vchk (fmt : Z) (out vs : list Z) (rom : smem) : bool :=
  let seed := vseed fmt (Z.of_nat (length out) + 1) vs rom in
  regions_wf (ss_mem seed) && rom_ok rom &&
  match vrun seed with
  | (ssF, RS_running) => vfin_ok seed ssF out
  | _ => false
  end.

Lemma vchk1 : vchk FMT_OOM1 render1 [A_TOOLNAME] ROM1 = true.
Proof. vm_compute. reflexivity. Qed.
Lemma vchk2_all :
  forallb (fun c => vchk FMT_OOM2 (render2 c (class_size c)) [REGION_MB; c; class_size c] ROM2) (map Z.of_nat (seq 1 31))
  = true.
Proof. vm_compute. reflexivity. Qed.
Lemma vchk2 : forall c, 1 <= c <= 31 -> vchk FMT_OOM2 (render2 c (class_size c)) [REGION_MB; c; class_size c] ROM2 = true.
Proof.
intros c Hc. pose proof vchk2_all as A. rewrite forallb_forall in A.
apply A. apply in_map_iff. exists (Z.to_nat c). split; [lia|]. apply in_seq. lia.
Qed.

Lemma rom_bytes_range :
  forallb (fun v => (0 <=? v) && (v <? 256)) (FMT1_BYTES ++ FMT2_BYTES ++ TOOL_BYTES) = true.
Proof. vm_compute. reflexivity. Qed.
Lemma ret_word : clookup tfibtbl_rtD A_VSN_RET = Some RET_WORD_r.
Proof. vm_compute. reflexivity. Qed.
