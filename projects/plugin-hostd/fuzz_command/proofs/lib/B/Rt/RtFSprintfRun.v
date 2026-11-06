(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/cgif/cgif_file_fuzzer/lib/A/AE30.v, with its module paths changed; 118 of its 153 lines of code are new or changed and 1523 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-10: relocated from lib/A/<same path> to fuzz_command.asan-ubsan by the image-B address relocator (the A-to-B address map, keyed by the image maps' symbol names and by code; GXA symbol keys kept), whose check table lists every changed numeral *)
(* The symbolic runs of the sprintf walk (code table RtFSprintfTbl.v), one stack region for both interceptors' frames,
   based at the entry sp (atom 2):
   - A: from the trampoline 0x451cc through ___interceptor_sprintf's prologue and va spill, TryAsanInitFromRtl
     (returns 1: the init cell 0xb1918 is 1), the call of the vsprintf interceptor 0x49bbc (ra 0x49fc4), its prologue,
     TryAsanInitFromRtl again, the check_printf flag (1), up to printf_common's entry 0x48d28 (ra 0x49c2c, a1 = f,
     a2 = the va pointer sp0 - 48). The region is [sp0 - 2256, sp0): the two frames (80 + 2160) and
     TryAsanInitFromRtl's 16 bytes.
   - B: after printf_common (region trimmed to [sp0 - 2240, sp0), caller-saved registers havocked from atom 32)
     through REAL(vsprintf) = musl vsprintf 0x9e194 and the vsnprintf trampoline 0x451c4 (`j`) to
     ___interceptor_vsnprintf 0x498a4 (a0 = d, a1 = 0x7fffffff, a2 = f, a3 = sp0 - 48, ra 0x49c44).
   - C: after the vsnprintf interceptor (atoms from 48; a0 = atom 52 = |T|): `bltz a0` not taken, `bltu ~s2, s1`
     not taken, to the check site 0x49c5c (s1 = |T| + 1, s2 = d, a0 = |T|).
   - D: from the check site's end 0x49ca4, a fresh state over the saved slots: the vsprintf epilogue, its `ret` to
     0x49fc4, the sprintf epilogue, stopping at its `ret` (jalr to the entry ra). *)
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0k YK0s YK0n YP0n YK1d.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP08 YP03 YP04 YP0g YP01.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YN3v YI04.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YG0v YO0f.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YK04 YA0i YA0n YA0o YA0p YA0q YA0m.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B Require Import YB1v YE34 YF0l YF0m YF0x YB1w YE20 YE2y.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Rt Require Import RtFSprintfTbl.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.

Definition SP_ENTRY : Z := 0x451cc.
Definition SP_PCOM : Z := 0x48d28.
Definition SP_RA_PCOM : Z := 0x49c2c.
Definition SP_VSNI : Z := 0x498a4.
Definition SP_RA_VSN : Z := 0x49c44.
Definition SP_CHK : Z := 0x49c5c.
Definition SP_CHK_END : Z := 0x49ca4.
(* the frames: ___interceptor_sprintf 80, ___interceptor_vsprintf 2032 + 128 *)
Definition SP_FR : Z := 2240.
Definition SP_STK : Z := 2256.

Definition RUN (s : sstate) := sym_runN tfibsegs tbl_spf FUEL s.
Definition RUNTO (stop : Z) (s : sstate) := sym_run_toN tfibsegs tbl_spf FUEL stop s.
Definition RG (s : sstate) (r : Z) : sv := sr_get (ss_regs s) (Z_to_bv 5 r).
Definition AC (s : sstate) (c : branch_cond) (a b : sv) : sstate := YP06.add_cond s (mkAC c a b).
Definition reg_is (ss : sstate) (r : Z) (v : sv) : bool := sv_eqb (RG ss r) v.
Definition chunk_is (off : Z) (v : sv) (c : YP09.chunk) : bool :=
(YP09.c_off c =? off) && match YP09.c_val c with CVal n e => N.eqb n 8 && sv_eqb e v | _ => false end.
Definition has_chunk (ss : sstate) (off : Z) (v : sv) : bool :=
match ss_mem ss with r :: _ => existsb (chunk_is off v) (YP09.r_chunks r) | [] => false end.
Lemma chunk_is_sound : forall off v c, chunk_is off v c = true -> c = YP09.mkChunk off (CVal 8 v).
Proof.
intros off v [o cv] Hc. unfold chunk_is in Hc. cbn [YP09.c_off YP09.c_val] in Hc. apply andb_prop in Hc as [Ho Hv].
apply Z.eqb_eq in Ho. destruct cv as [nn e| | |]; try discriminate. apply andb_prop in Hv as [Hn He].
apply N.eqb_eq in Hn. apply sv_eqb_eq in He. subst. reflexivity.
Qed.
Lemma has_chunk_sound : forall ss off v, has_chunk ss off v = true ->
  exists r rest, ss_mem ss = r :: rest /\ In (YP09.mkChunk off (CVal 8 v)) (YP09.r_chunks r).
Proof.
intros ss off v H. unfold has_chunk in H. destruct (ss_mem ss) as [|r rest] eqn:E; [discriminate|].
apply existsb_exists in H as (c & Hc & Hk). apply chunk_is_sound in Hk. subst c. exists r, rest. split; [reflexivity | exact Hc].
Qed.
(* the stack region is the first, based at atom 2, with these bounds *)
Definition stk_is (ss : sstate) (lo wlo : Z) : bool :=
match ss_mem ss with
| r :: _ => obase_eqb (YP09.r_base r) (Some 2%nat) && (YP09.r_lo r =? lo) && (YP09.r_hi r =? 0) &&
            (YP09.r_wlo r =? wlo) && (YP09.r_whi r =? 0)
| [] => false
end.
(* the writable windows of a state: the stack region's, or empty *)
Definition win_ok (lo : Z) (ss : sstate) : bool :=
forallb (fun t => win_eqb t (Some 2%nat, lo, 0) || (snd t <=? snd (fst t))) (windows (ss_mem ss)).

(* ---- A: entry to printf_common ---- *)
Definition stkA : YP09.region := YP09.mkRegion (Some 2%nat) (- SP_STK) 0 (- SP_STK) 0 [].
Definition factsA : list (nat * afact) := [(2%nat, mkAF (2^44) (2^47) 4)].
Definition ssA : sstate := mkSS SP_ENTRY sr_atoms (stkA :: map ro_region spf_rodata) None (mkFacts factsA [] []).
Definition eA : sstate := Eval vm_compute in fst (RUN ssA).
Lemma r_A : RUN ssA = (eA, RS_stopped SR_fetch). Proof. vm_compute. reflexivity. Qed.
(* the saved words and the va spill, below the entry sp: sprintf's ra s0 s1, the vsprintf interceptor's ra (0x49fc4)
   s0 (= f) s1 (= d) s2 .. s6, the va pointer at -80(s0) = sp0 - 160, and a2 .. a7 at sp0 - 48 .. sp0 - 8 *)
Definition SLOTS_A : list (Z * sv) :=
[(-56, SOff 1 0); (-64, SOff 8 0); (-72, SOff 9 0); (-88, SLit 0x49fc4); (-96, SOff 11 0); (-104, SOff 10 0);
 (-112, SOff 18 0); (-120, SOff 19 0); (-128, SOff 20 0); (-136, SOff 21 0); (-144, SOff 22 0);
 (-160, SOff 2 (-48));
 (-48, SOff 12 0); (-40, SOff 13 0); (-32, SOff 14 0); (-24, SOff 15 0); (-16, SOff 16 0); (-8, SOff 17 0)].
Definition KEPT_A : list Z := [3; 4; 23; 24; 25; 26; 27].
Definition shapeA (ss : sstate) : bool :=
(ss_pc ss =? SP_PCOM) && stk_is ss (- SP_STK) (- SP_STK) && win_ok (- SP_STK) ss &&
reg_is ss 1 (SLit SP_RA_PCOM) && reg_is ss 2 (SOff 2 (- SP_FR)) && reg_is ss 8 (SOff 2 (-80)) &&
reg_is ss 9 (SOff 11 0) && reg_is ss 11 (SOff 11 0) && reg_is ss 12 (SOff 2 (-48)) && reg_is ss 18 (SOff 10 0) &&
forallb (fun r => reg_is ss r (SOff (Z.to_nat r) 0)) KEPT_A &&
forallb (fun p => has_chunk ss (fst p) (snd p)) SLOTS_A &&
match ss_resv ss with None => true | Some _ => false end && ss_atoms_lt 32 ss.
Lemma shapeA_ok : shapeA eA = true. Proof. vm_compute. reflexivity. Qed.

(* ---- B: after printf_common, to the vsnprintf trampoline ---- *)
Definition memB : smem := Eval vm_compute in
match ss_mem eA with r0 :: rest => YI04.trim_lo r0 (- SP_FR) :: rest | [] => [] end.
Definition ssB : sstate := Eval vm_compute in ss_after_call eA memB 32 SP_RA_PCOM.
Definition eB : sstate := Eval vm_compute in fst (RUN ssB).
Lemma r_B : RUN ssB = (eB, RS_stopped SR_fetch). Proof. vm_compute. reflexivity. Qed.
Definition shapeB (ss : sstate) : bool :=
(ss_pc ss =? SP_VSNI) && stk_is ss (- SP_FR) (- SP_FR) && win_ok (- SP_FR) ss &&
reg_is ss 1 (SLit SP_RA_VSN) && reg_is ss 2 (SOff 2 (- SP_FR)) && reg_is ss 8 (SOff 2 (-80)) &&
reg_is ss 10 (SOff 10 0) && reg_is ss 11 (SLit 2147483647) && reg_is ss 12 (SOff 11 0) &&
reg_is ss 13 (SOff 2 (-48)) &&
reg_is ss 9 (SOff 11 0) && reg_is ss 18 (SOff 10 0) &&
forallb (fun r => reg_is ss r (SOff (Z.to_nat r) 0)) [3; 4; 20; 21; 22; 23; 24; 25; 26; 27] &&
forallb (fun p => has_chunk ss (fst p) (snd p)) SLOTS_A &&
match ss_resv ss with None => true | Some _ => false end && ss_atoms_lt 48 ss.
Lemma shapeB_ok : shapeB eB = true. Proof. vm_compute. reflexivity. Qed.
Lemma memB_sub : submem memB (ss_mem eA).
Proof.
change memB with (match ss_mem eA with r0 :: rest => YI04.trim_lo r0 (- SP_FR) :: rest | [] => [] end).
destruct (ss_mem eA) as [|r0 rest] eqn:E; [discriminate|].
apply submem_keep; [apply subregion_trim_lo | apply submem_refl].
Qed.
Lemma memB_ok : regions_wf memB = true /\ no_cdata memB = true /\ mem_atoms_lt 32 memB = true.
Proof. vm_compute. repeat split; reflexivity. Qed.
(* the regions kept across the two calls: the stack region [sp0 - 2240, sp0) with its words, and the read-only ones *)
Definition rB : YP09.region := Eval vm_compute in hd stkA memB.
Lemma memB_shape : memB = YP09.mkRegion (Some 2%nat) (- SP_FR) 0 (- SP_FR) 0 (YP09.r_chunks rB) :: map ro_region spf_rodata.
Proof. vm_compute. reflexivity. Qed.
Definition rE : YP09.region := Eval vm_compute in hd stkA (ss_mem eB).
Lemma eB_mem_shape : ss_mem eB = YP09.mkRegion (Some 2%nat) (- SP_FR) 0 (- SP_FR) 0 (YP09.r_chunks rE) :: map ro_region spf_rodata.
Proof. vm_compute. reflexivity. Qed.

(* ---- C: after the vsnprintf interceptor, to the check site ---- *)
Definition ssC : sstate := Eval vm_compute in ss_after_call eB (ss_mem eB) 48 SP_RA_VSN.
Lemma memC_ok : regions_wf (ss_mem eB) = true /\ no_cdata (ss_mem eB) = true /\ mem_atoms_lt 48 (ss_mem eB) = true.
Proof. vm_compute. repeat split; reflexivity. Qed.
Definition eC0 : sstate := Eval vm_compute in fst (RUN ssC).
Lemma r_C0 : RUN ssC = (eC0, RS_stopped (SR_branch BC_LT (SOff 52 0) (SLit 0))). Proof. vm_compute. reflexivity. Qed.
Definition ssC1 : sstate := Eval vm_compute in AC eC0 BC_GE (SOff 52 0) (SLit 0).
Definition eC1 : sstate := Eval vm_compute in fst (RUN ssC1).
Lemma r_C1 : RUN ssC1 = (eC1, RS_stopped (SR_branch BC_LTU (SAlu ALU_XOR (SOff 10 0) (SLit (-1)))
  (SAluw ALU_ADD (SOff 52 0) (SLit 1)))).
Proof. vm_compute. reflexivity. Qed.
Definition ssC2 : sstate := Eval vm_compute in
  AC eC1 BC_GEU (SAlu ALU_XOR (SOff 10 0) (SLit (-1))) (SAluw ALU_ADD (SOff 52 0) (SLit 1)).
Definition eC2 : sstate := Eval vm_compute in fst (RUNTO SP_CHK ssC2).
Lemma r_C2 : RUNTO SP_CHK ssC2 = (eC2, RS_running). Proof. vm_compute. reflexivity. Qed.
Definition shapeC (ss : sstate) : bool :=
(ss_pc ss =? SP_CHK) && stk_is ss (- SP_FR) (- SP_FR) && win_ok (- SP_FR) ss &&
reg_is ss 2 (SOff 2 (- SP_FR)) && reg_is ss 8 (SOff 2 (-80)) &&
reg_is ss 9 (SAluw ALU_ADD (SOff 52 0) (SLit 1)) && reg_is ss 10 (SOff 52 0) && reg_is ss 18 (SOff 10 0) &&
forallb (fun r => reg_is ss r (SOff (Z.to_nat r) 0)) [3; 4; 21; 22; 23; 24; 25; 26; 27] &&
forallb (fun p => has_chunk ss (fst p) (snd p)) SLOTS_A &&
match ss_resv ss with None => true | Some _ => false end.
Lemma shapeC_ok : shapeC eC2 = true. Proof. vm_compute. reflexivity. Qed.
Lemma winC_ok : win_ok (- SP_FR) ssC = true /\ win_ok (- SP_FR) ssC1 = true /\ win_ok (- SP_FR) ssC2 = true /\
  stk_is ssC (- SP_FR) (- SP_FR) = true /\ stk_is eC0 (- SP_FR) (- SP_FR) = true /\ stk_is eC1 (- SP_FR) (- SP_FR) = true.
Proof. vm_compute. repeat split; reflexivity. Qed.
Lemma winAB_ok : win_ok (- SP_STK) ssA = true /\ win_ok (- SP_FR) ssB = true /\ stk_is ssB (- SP_FR) (- SP_FR) = true.
Proof. vm_compute. repeat split; reflexivity. Qed.

(* ---- D: the two epilogues, from 0x49ca4, over a fresh state based at the check site's sp (= sp0 - 2240) ---- *)
(* the saved words at sp1 + (2240 + off) for SLOTS_A's offsets; the extra atoms 32 .. 41 hold the entry ra, s0, s1,
   f, d, s2 .. s6; the vsprintf interceptor's saved ra is the literal 0x49fc4 *)
Definition EPI_SLOTS : list (Z * sv) :=
[(-56, SOff 32 0); (-64, SOff 33 0); (-72, SOff 34 0); (-88, SLit 0x49fc4); (-96, SOff 35 0); (-104, SOff 36 0);
 (-112, SOff 37 0); (-120, SOff 38 0); (-128, SOff 39 0); (-136, SOff 40 0); (-144, SOff 41 0)].
Definition epi_chunks : list YP09.chunk := map (fun p => YP09.mkChunk (SP_FR + fst p) (CVal 8 (snd p))) EPI_SLOTS.
Definition ss_epi : sstate :=
mkSS SP_CHK_END sr_atoms [YP09.mkRegion (Some 2%nat) 0 SP_FR 0 0 epi_chunks] None
  (mkFacts [(2%nat, mkAF (2^43) (2^47) 4)] [] []).
Definition epi_e : sstate := Eval vm_compute in fst (RUN ss_epi).
Lemma r_epi : RUN ss_epi = (epi_e, RS_stopped (SR_jalr (SOff 32 0))). Proof. vm_compute. reflexivity. Qed.
Definition shapeE (ss : sstate) : bool :=
match clookup tbl_spf (ss_pc ss) with Some w => w =? RET_WORD_r | None => false end &&
reg_is ss 1 (SOff 32 0) && reg_is ss 2 (SOff 2 SP_FR) && reg_is ss 8 (SOff 33 0) && reg_is ss 9 (SOff 34 0) &&
reg_is ss 18 (SOff 37 0) && reg_is ss 19 (SOff 38 0) && reg_is ss 20 (SOff 39 0) && reg_is ss 21 (SOff 40 0) &&
reg_is ss 22 (SOff 41 0) && reg_is ss 10 (SOff 10 0) &&
forallb (fun r => reg_is ss r (SOff (Z.to_nat r) 0)) [3; 4; 23; 24; 25; 26; 27] &&
match ss_resv ss with None => true | Some _ => false end &&
forallb (fun t => snd t <=? snd (fst t)) (windows (ss_mem ss_epi)).
Lemma shapeE_ok : shapeE epi_e = true. Proof. vm_compute. reflexivity. Qed.
