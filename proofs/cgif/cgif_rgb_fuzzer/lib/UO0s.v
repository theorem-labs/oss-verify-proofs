(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OssFuzzTheorems.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YK11 YK0s YK0j YK15 YN06 YN02 YQ0b.
From OssFuzzTheorems.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import UH04 UH07 UH06.
From OssFuzzTheorems.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YP0j YP0g YP0c.
From OssFuzzTheorems.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YO04 YO29 UO08 UO0t UO0v UO0r.
From OssFuzzTheorems.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YN05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Open Scope Z_scope.
Section b. Context {fx : YK11.FPState} {rc : YN05.RunCeil}.
Definition mi_base (L : layout) (mi : option (nat * Z)) : Z := match mi with Some (k, _) => ly_reg L k | None => 0 end.
Definition mi_len (mi : option (nat * Z)) : Z := match mi with Some (_, len) => len | None => 0 end.
Record ntmidF (e : fentry) (Xz : list sptr) (fuel : nat) (L : layout) (A0 s : astate) (g : sptr) (mi : option (nat * Z))
(regs0 regs1 : bvmap 5 word) (mem0 mem1 : word -> option byte) (md : Model) (gv : Z) : Prop := {
nf_syms : syms_ok B1;
nf_layout : layout_ok L s;
nf_ctx : ly_ctx L = CTX;
nf_sec : 0 <= ly_sec L < 2 ^ 64;
nf_rep : memrepX B1 Xz L s mem1;
nf_statics : statics_ok B1 mem1;
nf_ledger : ledger_ok B1 L s md;
nf_md : m_halted md = None /\ m_vm_lazy md = [] /\ m_vm_materialized md = [];
nf_g : getr regs1 (nat_to_reg (aGF e)) = Z_to_bv 64 (ptr_addr L g);
nf_base : getr regs1 (nat_to_reg (aBASE e)) = Z_to_bv 64 (mi_base L mi);
nf_len : getr regs1 (nat_to_reg 11) = Z_to_bv 64 (mi_len mi);
nf_mi : 0 <= mi_base L mi < 2 ^ 64 /\ 0 <= mi_len mi < 2 ^ 64;
nf_s1 : getr regs1 (nat_to_reg 9) = Z_to_bv 64 GUARD;
nf_s2 : getr regs1 (nat_to_reg 18) = Z_to_bv 64 CTX;
nf_sp : getr regs1 (nat_to_reg 2) = Z_to_bv 64 (spZ regs0 - 96);
nf_keep : forall r, In r kept_regs -> getr regs1 (nat_to_reg r) = getr regs0 (nat_to_reg r);
nf_frame :
bytes_are mem1 (spZ regs0 - 48) 8 gv /\
bytes_are mem1 (spZ regs0 - 40) 8 (bv_unsigned (getr regs0 (nat_to_reg 19))) /\
bytes_are mem1 (spZ regs0 - 32) 8 (bv_unsigned (getr regs0 (nat_to_reg 18))) /\
bytes_are mem1 (spZ regs0 - 24) 8 (bv_unsigned (getr regs0 (nat_to_reg 9))) /\
bytes_are mem1 (spZ regs0 - 16) 8 (bv_unsigned (getr regs0 (nat_to_reg 8))) /\
bytes_are mem1 (spZ regs0 - 8) 8 (bv_unsigned (getr regs0 (nat_to_reg 1)));
nf_guard : word_mem ubs2segs mem1 GUARD gv;
nf_ret : YK0s.ret_ok (getr regs0 (nat_to_reg 1));
nf_tp : getr regs0 (nat_to_reg 4) = Z_to_bv 64 (ms_tp B1);
nf_spf : spZ regs0 mod 16 = 0 /\ alloc_ceiling + NT_FRAME * Z.of_nat (S fuel) <= spZ regs0 /\ spZ regs0 < 2 ^ 63;
nf_stkw : forall a, spZ regs0 - NT_FRAME * Z.of_nat (S fuel) <= a < spZ regs0 -> writable_at ubs2segs mem1 a;
nf_unch : forall a, 0 <= a < 2 ^ 64 -> ~ alloc_owned L A0 a -> ~ (spZ regs0 - NT_FRAME * Z.of_nat (S fuel) <= a < spZ regs0) ->
mbyte ubs2segs mem1 a = mbyte ubs2segs mem0 a /\ (writable_at ubs2segs mem0 a <-> writable_at ubs2segs mem1 a)
}.
End b.
