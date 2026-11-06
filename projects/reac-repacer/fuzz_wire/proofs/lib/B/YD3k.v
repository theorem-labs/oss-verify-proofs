(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: new file, written by a Theorem Labs lane *)
(* the asan-ubsan (lib/B here, lib/AU in fuzz_knock) twin of
   lib/A/AD3k.v (written by a Theorem Labs lane, the B2 walk prover, for
   another Theorem Labs lane), with AD3k's Qed proofs carried over. Outside comments it is AD3k.v with fuzz_wire.asan-ubsan's numbers (Create 0x7243c, its return 0x71eb8, Store 0x6f61c, its return 0x7195c, the return 0x71e40 of Put's call of StackDepotNode::store and kFACTS' DP / 4 = 395702, for AD3k's 0x7269c, 0x72118, 0x6f87c, 0x71bbc, 0x720a0 and 395670), YImgTop required from lib/B instead of lib/Reusable, and the name map lib/A/AXyz ->
   lib/B/YXyz here (lib/AU/YXyz in fuzz_knock, which keeps AWalkFw0), so AB1v AB1q AB1h AB1w AF0l AF0m AF0x AFl0 AFl3 AFek AFel AFem AD3a AD3g
   -> YB1v YB1q YB1h YB1w YF0l YF0m YF0x YFl0 YFl3 YFek YFel YFem YD3a YD3g (and AD3j -> YD3j in the comments); the other
   Reusable Requires are unchanged.
   rule 24: proves no function (kind: segment lemma).
   It is the CODE WALK of the FIRST StackDepotPut (StackDepotPut 0x71c18 in fuzz_wire.asan-ubsan (the donor fuzz_knock.asan-ubsan's 0x70ef0), which tail-jumps to
   StackDepotBase<StackDepotNode,1,20>::Put 0x71c38 (donor 0x70f10); donor pin sha256 f834165f5002...) around its two first-use
   callees, as segment lemmas in continuation-passing form. lib/B/YD3j.v (the statement tfib_depot_first_put_spec)
   composes K1-K3 with S7 (lib/B/YD3g.v tfib_tlm_create_nb_ok, TwoLevelMap::Create 0x7243c) and S1 (lib/B/YD3a.v
   tfib_store_ok, StackStore::Store 0x6f61c):
     K1 put_to_create        0x71c18 -> 0x7243c (Create's entry; ra 0x71eb8)
     K2 create_ret_to_store  0x71eb8 -> 0x6f61c (Store's entry, inside StackDepotNode::store 0x71930; ra 0x7195c)
     K3 store_ret_to_exit    0x7195c -> Put's return to its caller
   and K0 put_size0 is the size-0 early return (0x71c18 -> Put's return, a0 = 0).
   Each lemma: for any postcondition Q, if Q's run holds from every state that meets the boundary facts at the end PC,
   it holds from the start PC. The boundary facts of K1-K3 are the named Definitions at_create_call, at_store_call,
   put_exit. K1 reads the hash constants at 0x102d8 / 0x102f8 / 0x10398 through as_const (YD3j's premise).

   The numerals are re-measured on the asan-ubsan pin (sha256
   f834165f5002e65398e68d514ab2a5a5b10e53144f0b41b93ebbc6f895290e82) against the asan pin (sha256
   61768cf4739b7641c99c825dde45eddafc55b601d41109555be0272fc7ca4118), both fuzz_knock's; the YF0m.v lines below are its lib/AU file's:
   - theDepot (nm _ZN11__sanitizerL8theDepotE) 0x180418 -> 0x180458 and the StackStore object (nm
     _ZN11__sanitizerL10stackStoreE) 0x170408 -> 0x170448: the proofs read them as TFIB_DEPOT / as_depot and
     TFIB_STORE / as_store (YF0m.v:19, ts_depot / ts_store); the one literal derived from them is kFACTS' witness of
     4 | DP + 4 * Kbkt, DP / 4 = 393478 -> 393494 (0x180458 / 4). DP / SS below are the asan-ubsan values.
   - The hash constants stay at 0x102d8 / 0x102f8 / 0x10388 with the same values (YF0m.v:151-153).
   - Unchanged: the code addresses. As YD3j's header measures, StackDepotPut's 8 words differ only at 0x70ef8 (the
     theDepot addi), Put's 161 words (0x70f10-0x71194) and the lock's 36 (0x71684-0x71714) are byte-identical in both
     pins, and StackDepotNode::store's 23 (0x70c08-0x70c64) differ only at 0x70c24 / 0x70c28 (the stackStore auipc /
     addi); the walk decodes the asan-ubsan words through YFek's fetch table.
   In fuzz_knock, lib/AU/YF0m.v (TfibSyms, TFIB_DEPOT, TFIB_STORE) was not yet on this file's base: it was built from a file
   (a blob held in no published commit), a build-only input.

   THE CODE (addresses of the donor fuzz_knock ASan+UBSan image (pin sha256 f834165f5002), not fuzz_wire.asan-ubsan's; DP = its theDepot 0x180458, SS = its stackStore 0x170448; disassembly of
   that image's .text; the knock ASan image's listing is in lib/A/AD3k.v)
     0x70ef0 StackDepotPut: a2 := a1 (n); a1 := DP; a3 := a0 (buf); a0 := DP; a1 := buf; a3 := 0; j Put.
     0x70f10 Put: frame 0x70 at P = sp - 112: ra, s0-s9 at P + 0x68 .. P + 0x18; s0 := 0; s1 := DP; buf at P + 8, n at
       P + 16; n = 0 or buf = 0 -> return 0 (not taken: tr <> []).
     0x70f68-0x71000 the hash loop over the n trace words (constants DH_M / DH_M8 / DH_SEED from 0x102d8 / 0x102f8 /
       0x10388): s3 := h = tfib_dhash tr; s6 := 0xffff; s7 := 0x7fffffff.
     0x71004 s2 := DP + 4 * (h mod 2^20); lw tab[b1] = 0; s8 := DP + 0x400010 (map1_); s9 := 0; s4 := DP + 0x400008
       (mu_ = DP + tlm_mu); beqz -> 0x71088.
     0x7108c jal lock 0x71684 (frame 48 at P - 48): lr.w / sc.w tab[b1] := 0x80000000; returns the old word 0.
     0x71090 s5 := 0; beq 0, s9 -> 0x710c0: amoadd.w n_uniq_ids (DP + d_nuniq) 0 -> 1; s1 := 1; s7 := 1; a1 := 1 >> 16 = 0;
       ld map1_[0] = 0 -> 0x71188: a0 := s4; jal Create 0x71714 (ra 0x71190).                                   [K1]
     0x71190 j 0x710f8: s1 := x + 16 (x = Create's result, node 1); a2 := P + 8; a0 := s1; a1 := 0; a3 := h;
       jal StackDepotNode::store 0x70c08 (ra 0x71118): frame 32 at N = P - 32 (ra at N + 0x18, s0 at N + 0x10);
       s0 := x + 16; node.hash := h (sd at x + 16); pack := 0 at N + 8; a0 := SS; a1 := P + 8; a2 := N + 8;
       jal Store 0x6e8f4 (ra 0x70c34).                                                                        [K2]
     0x70c34 ld pack (0); node.store_id := a0 (sw at x + 28); pack = 0 -> restore ra, s0; ret to 0x71118:
       node.link := s5 = 0 (sw at x + 24); fence; a0 := 1; tab[b1] := 1 (the unlock); s0 = 0 -> restore ra, s0-s9;
       ret (a0 = 1).                                                                                           [K3]
   Stack below Put's entry sp: Put 112, the lock 48 more (160); the callees' bands are S7's and S1's.

   The walk uses the symbolic runner of YFem.v (the mapped-case Put) with first-use seeds: YFem's Section s lemmas
   assume layout_ok and YFek's sstates carry DF_fixed (NB, SB >= 4096, n_uniq_ids >= 1), false at the first Put, so
   the seeds, the loop state and the frame invariant are rebuilt here; YFem's hash_loop is ported. *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/libreac/fuzz_knock/lib/AU/YD3k.v at 88154566652a (donor image sha256 f834165f5002), with its module paths changed, B/YB1v imported for AU/AWalkFw0, names TfibSyms -> WireSyms, its addresses moved to reac-repacer/fuzz_wire's ASan+UBSan build, YImgTop taken from lib/B instead of lib/Reusable and its proofs' unfolds of YImgTop.IMG_TOP (in 5 of the donor's unfold steps) removed (this unit's lib/B/YImgTop.v states the image bounds as notations, fuzz_knock's lib/Reusable/YImgTop.v as definitions). *)
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.Reusable Require YZ00.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.B Require YImgTop.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YP0j.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.Reusable Require Import YN3v YI04 YO0d.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.Reusable Require Import YK04 YA0i YA0n YA0o YA0p YA0q.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0v YG0n YG0d.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.B Require Import YB1v YB1q YB1h YB1w YF0l YF0m YF0x YFl0 YFl3 YFek YFel.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.B Require Import YD3g.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.B Require YFem YD3a.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.Reusable Require YN0d.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.Reusable Require Import YL02 YL09.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Open Scope Z_scope.

(* ===== The symbolic states of the walk (fetch table: YFek's tfibtbl_rtD, which covers StackDepotPut / Put
   0x70ef0-0x71194, find / lock / Create 0x715d0-0x71814, StackDepotNode::store 0x70c08-0x70c64 and Store). ===== *)
Definition ch8 (o : Z) (e : sv) : YP09.chunk := YP09.mkChunk o (CVal 8 e).
(* K2 at 0x71190: env Ereg regs [] (atoms 0-31 = the registers at 0x71190); s1 = 1 and s6 = 0xffff pinned (the node
   address x + 16 * (1 & 0xffff) folds to x + 16); StackDepotNode::store's frame [sp - 32, sp) and node 1's hash word. *)
Definition R_K2S : YP09.region := YP09.mkRegion (Some 2%nat) (-32) 0 (-32) 0 [].
Definition R_K2N : YP09.region := YP09.mkRegion (Some 10%nat) 16 24 16 24 [].
Definition SS_K2 : sstate :=
  mkSS 0x71eb8 (sr_set (sr_set sr_atoms 9%bv (SLit 1)) 22%bv (SLit 0xffff)) [R_K2S; R_K2N] None (mkFacts [] [] []).
(* K3 at 0x70c34: env Ereg regs [ra; s0; s1; s2; ...; s9 of Put's entry] (atoms 32-42); sp = N; s1 aliased to s0
   (both x + 16); the frames of StackDepotNode::store and Put read, node 1's link / store_id and tab[b1] written. *)
Definition R_K3S : YP09.region := YP09.mkRegion (Some 2%nat) 0 144 0 0
  [ch8 8 (SLit 0); ch8 16 (SLit 0); ch8 24 (SLit 0x71e40); ch8 56 (SOff 42 0); ch8 64 (SOff 41 0); ch8 72 (SOff 40 0);
   ch8 80 (SOff 39 0); ch8 88 (SOff 38 0); ch8 96 (SOff 37 0); ch8 104 (SOff 36 0); ch8 112 (SOff 35 0);
   ch8 120 (SOff 34 0); ch8 128 (SOff 33 0); ch8 136 (SOff 32 0)].
Definition R_K3N : YP09.region := YP09.mkRegion (Some 8%nat) 8 16 8 16 [].
Definition R_K3T : YP09.region := YP09.mkRegion (Some 18%nat) 0 4 0 4 [].
Definition SS_K3 : sstate := mkSS 0x7195c (sr_set sr_atoms 9%bv (SOff 8 0)) [R_K3S; R_K3N; R_K3T] None (mkFacts [] [] []).
(* K0 at 0x70ef0 with size 0: env Ereg regs []; a1 = n pinned to 0 (so sext.w a3, a2 = 0 and beqz a3 -> 0x71134);
   Put's frame [sp - 112, sp) written and reloaded. *)
Definition R_Z0 : YP09.region := YP09.mkRegion (Some 2%nat) (-112) 0 (-112) 0 [].
Definition SS_Z0 : sstate := mkSS A_StackDepotPut (sr_set sr_atoms 11%bv (SLit 0)) [R_Z0] None (mkFacts [] [] []).
(* YD3g.v's rreg7 (local to its section): a register of the state, as the denotation of its symbolic value. *)
Ltac rregk HS r R :=
  lazymatch type of HS with st_ok ?segs ?E ?ss (restrict ?H ?ms) =>
  let e := eval vm_compute in (sr_get (ss_regs ss) r) in
  pose proof (st_ok_reg_denot H E ss ms r HS) as R; change (sr_get (ss_regs ss) r) with e in R end.
Definition EK2 (regs : bvmap 5 word) : env := Ereg regs [].
Definition EK3 (regs regs0 : bvmap 5 word) : env :=
  Ereg regs [getr regs0 1%bv; getr regs0 8%bv; getr regs0 9%bv; getr regs0 18%bv; getr regs0 19%bv; getr regs0 20%bv;
             getr regs0 21%bv; getr regs0 22%bv; getr regs0 23%bv; getr regs0 24%bv; getr regs0 25%bv].

(* K1 from 0x70ef0: env Ereg regs [0; 0; 0; 0; h; S2] (atom 36 = aHASH = h, atom 37 = aS2 = DP + 4 * b1, YFek's
   numbering); the stack window [sp - DEP_STK, sp), the hash constants, and the empty depot's three cells as literals:
   map1_[0] = 0 (read only), n_uniq_ids = 0 and tab[b1] = 0 (written). No depot block, no DF_fixed. *)
Definition KNUQ : Z := TFIB_DEPOT + d_nuniq.
Definition R_TABk : YP09.region := YP09.mkRegion (Some aS2) 0 4 0 4 [YP09.mkChunk 0 (CVal 4 (SLit 0))].
Definition R_NUQk : YP09.region := YP09.mkRegion None KNUQ (KNUQ + 4) KNUQ (KNUQ + 4) [YP09.mkChunk KNUQ (CVal 4 (SLit 0))].
Definition R_MAPk : YP09.region := lit8 (TFIB_DEPOT + d_map1) 0.
Definition KFIX : smem := D_consts ++ [R_MAPk; R_NUQk; R_TABk].
Definition KF_fixed : list (nat * afact) :=
  [(2%nat, mkAF (kHighMemBeg + DEP_STK) kHighMemEnd 4); (10%nat, mkAF kHighMemBeg (kHighMemEnd - 240) 3);
   (11%nat, mkAF 1 30 0); (aHASH, u64f); (aS2, mkAF TFIB_DEPOT (TFIB_DEPOT + 4 * 2 ^ 20 - 4) 2)].
Definition SS_K0 : sstate := mkSS A_StackDepotPut sr_atoms (R_DS :: KFIX) None (mkFacts KF_fixed [] []).
Definition S_KH0 : sstate := Eval vm_compute in runto_d A_HLOOP SS_K0.
(* the hash loop's state at 0x70fa0 (YFek's HREGS / HF with the first-use fixed facts) *)
Definition KHREGS : list sv :=
  sr_set (sr_set (sr_set (sr_set (sr_set (sr_set (ss_regs S_KH0) 11%bv (SOff dP 0)) 12%bv (SOff dH 0)) 13%bv (SLit 0))
  14%bv (SOff dE 0)) 15%bv (SOff 46%nat 0)) 16%bv (SOff 47%nat 0).
Definition KHF : facts := mkFacts (KF_fixed ++ [(dW, u64f); (dH, u64f); (dP, mkAF kHighMemBeg (kHighMemEnd - 8) 3);
  (dE, mkAF kHighMemBeg kHighMemEnd 3); (46%nat, u64f); (47%nat, u64f)]) [] [].
Definition KR_DS' : YP09.region := Eval vm_compute in hd R_DS (ss_mem S_KH0).
Definition KFIX' : smem := KR_DS' :: KFIX.
Definition S_KH : sstate := mkSS A_HLOOP KHREGS (R_W :: KFIX') None KHF.
Definition S_KHT : sstate := Eval vm_compute in run_d S_KH.
Definition S_KHX : sstate := Eval vm_compute in run_d (add_cond S_KHT c_hexit).
(* after the loop, at 0x71010: s3 := h and s2 := S2 pinned (YFem's two pins) *)
Definition S_KP : sstate := Eval vm_compute in pin (pin S_KHX 19%bv (SOff aHASH 0)) 18%bv (SOff aS2 0).
(* the windows K1 writes: Put's and the lock's frames in [sp - DEP_STK, sp), tab[b1], n_uniq_ids *)
Definition KWSK : list (option nat * Z * Z) := [(Some 2%nat, - DEP_STK, 0); (Some aS2, 0, 4); (None, KNUQ, KNUQ + 4)].
Definition kwsk_ok (rs : smem) : bool :=
  forallb (fun t => existsb (win_eqb t) KWSK || (snd t <=? snd (fst t))) (windows rs).
Ltac kred_sr :=
  lazymatch goal with |- _ = U _ (sr_get ?rs ?r) => let e := eval vm_compute in (sr_get rs r) in change (sr_get rs r) with e end.

Section kh. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
(* YFem's val_mem_mod64 / agree_pd_havoc / JKf / dh_step_mod, restated without YFem's Section s arguments. *)
Lemma kval_mem_mod64 : forall (m : word -> option byte) a v, val_mem tfibsegs m a 8 v -> val_mem tfibsegs m a 8 (v mod 2 ^ 64).
Proof.
intros m a v H k Hk. rewrite (H k Hk). f_equal. f_equal. unfold YO0f.le_byte. change (2 ^ (8 * Z.of_nat 8)) with (2 ^ 64).
rewrite Z.mod_mod by lia. reflexivity.
Qed.
Lemma kagree_pd_havoc : forall E k ws, (42 <= k)%nat -> env_agree_pd YFem.LT42 PT E (havoc E k ws).
Proof.
intros E k ws Hk. split; [| intros d _; rewrite ed_havoc; reflexivity].
intros n Hn. unfold YFem.LT42 in Hn. apply Nat.ltb_lt in Hn. rewrite ew_havoc_old by lia. reflexivity.
Qed.
Lemma kJKf : forall E' k (w : word), ew E' k = w -> afact_ok E' k u64f.
Proof.
intros E' k w Hk. unfold afact_ok, u64f. cbn [af_lo af_hi af_al2]. pose proof (u64_range (ew E' k)).
split; [lia|]. split; [apply Z.mod_1_r | lia].
Qed.
Lemma kdh_step_mod : forall h w, dh_step h (w mod 2 ^ 64) = dh_step h w.
Proof. intros h w. unfold dh_step, dh_mul. rewrite Z.mul_mod_idemp_l by lia. reflexivity. Qed.
(* YFel's SRr_run_toG for the shadow-normalizing runner (the amoadd.w on n_uniq_ids needs it). *)
Lemma SRr_run_to_shG : forall tbl, table_ok tfibsegs tbl -> forall W n stop E ss ss' st ms model Q,
  st_ok tfibsegs E ss (restrict (w_H W) ms) -> sym_run_toN_sh tfibsegs tbl n stop ss = (ss', st) ->
  run_postG W E ss ss' st ms model Q -> SRr tfibsegs W (mkCfg ms model) Q.
Proof.
intros tbl tbl_ok W n stop E ss ss' st ms model Q HS Hrun Hk.
destruct (msteps_run_to_sh tfibsegs tbl tbl_ok n stop E ss ss' st _ HS Hrun) as (msr' & Hms & HS' & Hfr).
exact (SRr_of_restricted_chainG W E ss ss' st ms msr' model Q Hms HS' Hfr Hk).
Qed.
End kh.
Ltac srr_run_to_shG tblok HS stop :=
  lazymatch type of HS with
  | st_ok ?segs ?E ?ss (restrict (w_H ?W) ?ms) =>
    lazymatch type of tblok with
    | table_ok _ ?tbl =>
      let r := eval vm_compute in (sym_run_toN_sh segs tbl FUEL stop ss) in
      lazymatch r with
      | (?ss', ?st) =>
        let Hrun := fresh "Hrun" in
        assert (Hrun : sym_run_toN_sh segs tbl FUEL stop ss = (ss', st)) by (vm_compute; reflexivity);
        eapply (SRr_run_to_shG tbl tblok W FUEL stop E ss ss' st ms _ _ HS Hrun);
        clear Hrun HS; cbv beta iota; srr_after_runG HS
      end
    end
  end.

Section g. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable B : asyms.
Hypothesis HB : WireSyms B.
Hypothesis HDH : forall t, as_dhash B t = YF0p.tfib_dhash t.

(* ===== Boundary facts. regs0 = Put's entry registers (at StackDepotPut 0x70ef0), sp = spZ regs0, P = sp - 112 (Put's
   frame), N = P - 32 (StackDepotNode::store's frame); h = tfib_dhash tr, b1 = (h mod 2^64) mod d_tab_words (the
   bucket; tab[b1] at as_depot B + 4 * b1). ===== *)

(* Put's saved registers in its frame: ra, s0-s9 at P + 0x68 .. P + 0x18 (8 bytes each). *)
Definition put_saved (H : word -> bool) (mem : word -> option byte) (regs0 : bvmap 5 word) : Prop :=
  let P := spZ regs0 - 112 in let m := mrestrict H mem in
  val_mem tfibsegs m (P + 0x68) 8 (bv_unsigned (getr regs0 1)) /\ val_mem tfibsegs m (P + 0x60) 8 (bv_unsigned (getr regs0 8)) /\
  val_mem tfibsegs m (P + 0x58) 8 (bv_unsigned (getr regs0 9)) /\ val_mem tfibsegs m (P + 0x50) 8 (bv_unsigned (getr regs0 18)) /\
  val_mem tfibsegs m (P + 0x48) 8 (bv_unsigned (getr regs0 19)) /\ val_mem tfibsegs m (P + 0x40) 8 (bv_unsigned (getr regs0 20)) /\
  val_mem tfibsegs m (P + 0x38) 8 (bv_unsigned (getr regs0 21)) /\ val_mem tfibsegs m (P + 0x30) 8 (bv_unsigned (getr regs0 22)) /\
  val_mem tfibsegs m (P + 0x28) 8 (bv_unsigned (getr regs0 23)) /\ val_mem tfibsegs m (P + 0x20) 8 (bv_unsigned (getr regs0 24)) /\
  val_mem tfibsegs m (P + 0x18) 8 (bv_unsigned (getr regs0 25)).

(* Put's whole frame: the saved registers and the StackTrace {trace = buf, size word = n} at P + 8 (Store's targ). *)
Definition put_frame (H : word -> bool) (mem : word -> option byte) (regs0 : bvmap 5 word) (buf : Z) (tr : list Z) : Prop :=
  let P := spZ regs0 - 112 in let m := mrestrict H mem in
  put_saved H mem regs0 /\ val_mem tfibsegs m (P + 8) 8 buf /\ val_mem tfibsegs m (P + 16) 8 (Z.of_nat (length tr)).

(* Put's callee-saved registers s2-s9 after the n_uniq_ids bump (they hold to Put's epilogue), and gp, tp, s10, s11
   as at entry. *)
Definition put_cs (rg regs0 : bvmap 5 word) (tr : list Z) : Prop :=
  let h := YF0p.tfib_dhash tr in let b1 := (h mod 2 ^ 64) mod d_tab_words in let DP := as_depot B in
  getr rg 18 = Z_to_bv 64 (DP + 4 * b1) /\ getr rg 19 = Z_to_bv 64 h /\ getr rg 20 = Z_to_bv 64 (DP + tlm_mu) /\
  getr rg 21 = Z_to_bv 64 0 /\ getr rg 22 = Z_to_bv 64 0xffff /\ getr rg 23 = Z_to_bv 64 1 /\
  getr rg 24 = Z_to_bv 64 (DP + d_map1) /\ getr rg 25 = Z_to_bv 64 0 /\
  getr rg 3 = getr regs0 3 /\ getr rg 4 = getr regs0 4 /\ getr rg 26 = getr regs0 26 /\ getr rg 27 = getr regs0 27.

(* K1's boundary, at TwoLevelMap::Create's entry 0x71714 (S7's pre: a0 = DP + tlm_mu, a1 = 0, ra = 0x71190). *)
Definition at_create_call (regs0 : bvmap 5 word) (H : word -> bool) (mem0 : word -> option byte) (buf : Z) (tr : list Z)
  (regs1 : bvmap 5 word) (mem1 : word -> option byte) : Prop :=
  let sp := spZ regs0 in let P := sp - 112 in let h := YF0p.tfib_dhash tr in let b1 := (h mod 2 ^ 64) mod d_tab_words in
  let DP := as_depot B in let m1 := mrestrict H mem1 in
  getr regs1 1 = Z_to_bv 64 0x71eb8 /\ getr regs1 2 = Z_to_bv 64 P /\
  getr regs1 10 = Z_to_bv 64 (DP + tlm_mu) /\ getr regs1 11 = Z_to_bv 64 0 /\
  getr regs1 8 = Z_to_bv 64 0 /\ getr regs1 9 = Z_to_bv 64 1 /\ put_cs regs1 regs0 tr /\
  put_frame H mem1 regs0 buf tr /\
  val_mem tfibsegs m1 (DP + 4 * b1) 4 0x80000000 /\ val_mem tfibsegs m1 (DP + d_nuniq) 4 1 /\
  (forall i, (i < length tr)%nat -> val_mem tfibsegs m1 (buf + 8 * Z.of_nat i) 8 (nth i tr 0)) /\
  (forall a : word, ~ (sp - DEP_STK <= bv_unsigned a < sp) -> ~ (DP + 4 * b1 <= bv_unsigned a < DP + 4 * b1 + 4) ->
     ~ (DP + d_nuniq <= bv_unsigned a < DP + d_nuniq + 4) -> mem1 a = mem0 a) /\
  (forall a, apresent H mem0 a -> apresent H mem1 a).

(* K2's boundary, at StackStore::Store's entry 0x6e8f4 (S1's pre: a0 = SS, a1 = targ = P + 8, a2 = pk = N + 8,
   ra = 0x70c34), x = Create's result (node 1 at x + 16). *)
Definition at_store_call (regs0 : bvmap 5 word) (H : word -> bool) (mem0 : word -> option byte) (buf : Z) (tr : list Z)
  (x : Z) (regs1 : bvmap 5 word) (mem1 : word -> option byte) : Prop :=
  let sp := spZ regs0 in let P := sp - 112 in let N := P - 32 in let m1 := mrestrict H mem1 in
  getr regs1 1 = Z_to_bv 64 0x7195c /\ getr regs1 2 = Z_to_bv 64 N /\ getr regs1 10 = Z_to_bv 64 (as_store B) /\
  getr regs1 11 = Z_to_bv 64 (P + 8) /\ getr regs1 12 = Z_to_bv 64 (N + 8) /\
  getr regs1 8 = Z_to_bv 64 (x + 16) /\ getr regs1 9 = Z_to_bv 64 (x + 16) /\ put_cs regs1 regs0 tr /\
  val_mem tfibsegs m1 (N + 0x18) 8 0x71e40 /\ val_mem tfibsegs m1 (N + 0x10) 8 0 /\ val_mem tfibsegs m1 (N + 8) 8 0 /\
  put_frame H mem1 regs0 buf tr /\
  val_mem tfibsegs m1 (x + 16) 8 (YF0p.tfib_dhash tr) /\
  (forall a : word, ~ (sp - DEP_STK <= bv_unsigned a < sp) -> ~ (x + 16 <= bv_unsigned a < x + 24) -> mem1 a = mem0 a) /\
  (forall a, apresent H mem0 a -> apresent H mem1 a).

(* K3's end, Put's return (pc = regs0's ra): a0 = 1 (the new id), the callee-saved registers of Put's entry; node 1's
   store_id (x + 28) = 1 and link (x + 24) = 0, tab[b1] = 1 (the unlock); nothing else written. *)
Definition put_exit (regs0 : bvmap 5 word) (H : word -> bool) (mem0 : word -> option byte) (tr : list Z) (x : Z)
  (regs1 : bvmap 5 word) (mem1 : word -> option byte) : Prop :=
  let h := YF0p.tfib_dhash tr in let b1 := (h mod 2 ^ 64) mod d_tab_words in let S2 := as_depot B + 4 * b1 in
  let m1 := mrestrict H mem1 in
  getr regs1 10 = Z_to_bv 64 1 /\ regs_preserved regs0 regs1 /\
  val_mem tfibsegs m1 (x + 28) 4 1 /\ val_mem tfibsegs m1 (x + 24) 4 0 /\ val_mem tfibsegs m1 S2 4 1 /\
  (forall a : word, ~ (x + 24 <= bv_unsigned a < x + 32) -> ~ (S2 <= bv_unsigned a < S2 + 4) -> mem1 a = mem0 a) /\
  (forall a, apresent H mem0 a -> apresent H mem1 a).

(* ===== K1's walk: YFem's entry_phase / reabs_H / hash_loop and the miss path of B_phase / find_loop / ins_phase,
   rebuilt on the first-use seed SS_K0 (no depot block; tab[b1], n_uniq_ids and map1_[0] literal 0). ===== *)
Section k1.
Variables (W : world tfibsegs) (regs : bvmap 5 word) (mem : word -> option byte) (md : Model) (ly : alayout)
  (buf : Z) (tr : list Z) (Q : world tfibsegs -> config -> Prop).
#[local] Notation Hd := (w_H W).
#[local] Notation m0 := (mrestrict (w_H W) mem).
#[local] Notation sp := (spZ regs).
Hypotheses (R10 : getr regs 10%bv = Z_to_bv 64 buf) (R11 : getr regs 11%bv = Z_to_bv 64 (Z.of_nat (length tr))).
Hypothesis Hwords : forall i, (i < length tr)%nat -> val_mem tfibsegs m0 (buf + 8 * Z.of_nat i) 8 (nth i tr 0).
Hypotheses (Hbuf8 : buf mod 8 = 0) (Hbuflo : ly_stk_lo ly <= buf) (Hbufhi : buf + 8 * 30 <= ly_stk_hi ly)
  (Hbuf_sp : buf + 8 * 30 <= sp - DEP_STK \/ sp <= buf).
Hypotheses (Hsp16 : sp mod 16 = 0) (Hstk0 : kHighMemBeg <= ly_stk_lo ly) (Hstk1 : ly_stk_hi ly <= kHighMemEnd)
  (Hsplo : ly_stk_lo ly <= sp - DEP_STK) (Hsphi : sp <= ly_stk_hi ly)
  (P_stk : forall a, sp - DEP_STK <= a < sp -> apresent Hd mem a).
Hypotheses (Htr : In tr (as_universe B)) (Hne : tr <> []).
Hypothesis HTAB : forall b, 0 <= b < d_tab_words -> rd32 (aview tfibsegs Hd mem) (as_depot B + 4 * b) 0.
Hypotheses (HNUQ : val_mem tfibsegs m0 (as_depot B + d_nuniq) 4 0) (HMAP : val_mem tfibsegs m0 (as_depot B + d_map1) 8 0).
Hypothesis HCONST : Forall (cell_holds B ly (aview tfibsegs Hd mem)) (as_const B ly).
Hypothesis K : forall regs1 mem1 mat, at_create_call regs Hd mem buf tr regs1 mem1 ->
  SRr tfibsegs W (mkCfg (mkst regs1 (Z_to_bv 64 tfib_A_TwoLevelMap_Create_71714) mem1 (seg_rom tfibsegs))
                        (with_vm_backing (m_vm_lazy md) mat md)) Q.

Definition KHSH : Z := YF0p.tfib_dhash tr.
Definition Kbkt : Z := KHSH mod d_tab_words.
Definition KS2 : Z := TFIB_DEPOT + 4 * Kbkt.

Lemma ktr_len : (1 <= length tr <= 30)%nat.
Proof.
pose proof (ts_universe B HB) as (_ & HU & _).
assert (L : (length tr <= 30)%nat) by exact (proj1 (Forall_forall _ _) HU tr Htr).
assert (L0 : length tr <> 0%nat) by (intros E; apply Hne; apply length_zero_iff_nil; exact E). lia.
Qed.
Lemma kzone :
  0x10007fff8000 <= sp - 512 /\ sp <= 0x800000000000 /\ 0x10007fff8000 <= buf /\ buf + 240 <= 0x800000000000 /\
  (buf + 240 <= sp - 512 \/ sp <= buf) /\ (1 <= length tr <= 30)%nat /\ 0 <= KHSH < 2 ^ 64 /\ 0 <= Kbkt < 1048576 /\
  sp mod 16 = 0 /\ buf mod 8 = 0.
Proof.
pose proof ktr_len as TL. pose proof (YFem.tfib_dhash_u64 tr) as HR.
assert (KR : 0 <= Kbkt < 1048576) by (unfold Kbkt, d_tab_words; apply Z.mod_pos_bound; lia).
pose proof Hbuf_sp as C5. pose proof Hstk0 as C1. pose proof Hstk1 as C2. pose proof Hsplo as C3. pose proof Hsphi as C4.
pose proof Hbuflo as C6. pose proof Hbufhi as C7. pose proof Hsp16 as C8. pose proof Hbuf8 as C9.
unfold KHSH in *. unfold kHighMemBeg, kHighMemEnd, DEP_STK in *.
clear - TL HR KR C1 C2 C3 C4 C5 C6 C7 C8 C9. repeat split; lia.
Qed.
Ltac kz := pose proof kzone as (Z1 & Z2 & Z3 & Z4 & Z5 & Z6 & Z7 & Z8 & Z9 & Z10).

Definition KXW : list word := [Z_to_bv 64 0; Z_to_bv 64 0; Z_to_bv 64 0; Z_to_bv 64 0; Z_to_bv 64 KHSH; Z_to_bv 64 KS2].
Definition KE0 : env := Ereg regs KXW.
Lemma KE36 : ew KE0 aHASH = Z_to_bv 64 KHSH. Proof. reflexivity. Qed.
Lemma KE37 : ew KE0 aS2 = Z_to_bv 64 KS2. Proof. reflexivity. Qed.
Lemma KEr (k : nat) (r : bv 5) : Z.of_nat k = bv_unsigned r -> ew KE0 k = getr regs r.
Proof. intros Hk. exact (ew_Ereg_nat regs KXW k r Hk). Qed.
Definition kenvD (E : env) : Prop := forall k, (k < K_D)%nat -> ew E k = ew KE0 k.
Lemma kenvD_E0 : kenvD KE0. Proof. intros k _. reflexivity. Qed.
Lemma kenvD_havoc : forall E k ws, kenvD E -> (K_D <= k)%nat -> kenvD (havoc E k ws).
Proof. intros E k ws HE Hk j Hj. rewrite ew_havoc_old by lia. exact (HE j Hj). Qed.
Record kfixedU (E : env) : Prop := {
  KU2 : bv_unsigned (ew E 2) = sp; KU10 : bv_unsigned (ew E 10) = buf; KU11 : bv_unsigned (ew E 11) = Z.of_nat (length tr);
  KU36 : bv_unsigned (ew E aHASH) = KHSH; KU37 : bv_unsigned (ew E aS2) = KS2 }.
Lemma kfixedU_of : forall E, kenvD E -> kfixedU E.
Proof.
intros E HE. kz.
assert (L : forall k z, (k < K_D)%nat -> ew KE0 k = Z_to_bv 64 z -> 0 <= z < 2 ^ 64 -> bv_unsigned (ew E k) = z).
{ intros k z Hk Hz Hr. rewrite (HE k Hk), Hz. apply unsigned_lit_small. exact Hr. }
unfold K_D in L. constructor.
- rewrite (HE 2%nat ltac:(unfold K_D; lia)), (KEr 2 2%bv eq_refl). reflexivity.
- apply (L 10%nat buf ltac:(lia)); [rewrite <- R10; exact (KEr 10 10%bv eq_refl) | lia].
- apply (L 11%nat _ ltac:(lia)); [rewrite <- R11; exact (KEr 11 11%bv eq_refl) | lia].
- apply (L aHASH _ ltac:(unfold aHASH; lia) KE36). exact Z7.
- apply (L aS2 _ ltac:(unfold aS2; lia) KE37). unfold KS2, TFIB_DEPOT. lia.
Qed.
Ltac kfixu HE := pose proof (kfixedU_of _ HE) as [V2 V10 V11 V36 V37];
  pose proof V36 as V36'; pose proof V37 as V37'; unfold aHASH in V36'; unfold aS2 in V37'.

(* ---- the seed at 0x70ef0 ---- *)
Lemma kconst : forall a (w : nat) v, cell_lookup (Tfib_const ly) (ANum a) = Some (ACell (ANum a) w (AV (ANum v))) ->
  val_mem tfibsegs m0 a w v.
Proof. intros a w v E. exact (YFem.const_val B HB W ly mem HCONST a w v E). Qed.
Lemma kREG0 : Forall (region_ok tfibsegs KE0 m0) (R_DS :: KFIX).
Proof.
kz. pose proof (ts_depot B HB) as ED.
assert (VT : val_mem tfibsegs m0 KS2 4 0).
{ unfold KS2. rewrite <- ED. apply (YFem.rd32_val_mem W mem). apply HTAB. unfold Kbkt, d_tab_words. apply Z.mod_pos_bound. lia. }
pose proof HNUQ as VN. pose proof HMAP as VM. rewrite ED in VN, VM.
unfold R_DS, KFIX, D_consts, R_MAPk, R_NUQk, R_TABk, lit8. cbn [app].
apply Forall_cons.
{ apply (region_ok_stack tfibsegs KE0 m0 2 sp (- DEP_STK)); [rewrite (KEr 2 2%bv eq_refl); reflexivity | unfold DEP_STK; lia
  | pose proof (u64_range (getr regs 2%bv)) as SR; unfold spZ in *; lia |].
  intros a Ha. apply YD3a.apresent_wr. apply P_stk. lia. }
apply Forall_cons. { apply (region_ok_lit KE0 m0 0x102d8 8 DH_M); [apply kconst; reflexivity | unfold DH_M; cbn; lia | cbn; lia | lia | cbn; lia]. }
apply Forall_cons. { apply (region_ok_lit KE0 m0 0x102f8 8 DH_M8); [apply kconst; reflexivity | unfold DH_M8; cbn; lia | cbn; lia | lia | cbn; lia]. }
apply Forall_cons. { apply (region_ok_lit KE0 m0 0x10398 8 DH_SEED); [apply kconst; reflexivity | unfold DH_SEED; cbn; lia | cbn; lia | lia | cbn; lia]. }
apply Forall_cons.
{ apply (region_ok_lit KE0 m0 (TFIB_DEPOT + d_map1) 8 0); [exact VM | cbn; lia | cbn; lia | unfold TFIB_DEPOT, d_map1; lia
  | unfold TFIB_DEPOT, d_map1; cbn; lia]. }
apply Forall_cons.
{ unfold KNUQ. apply (region_ok_rwlit KE0 m0 (TFIB_DEPOT + d_nuniq) 4 0); [exact VN | cbn; lia | cbn; lia
  | unfold TFIB_DEPOT, d_nuniq; lia | unfold TFIB_DEPOT, d_nuniq; cbn; lia]. }
apply Forall_cons.
{ unfold region_ok. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
  rewrite KE37, unsigned_lit_small by (unfold KS2, TFIB_DEPOT; lia).
  split; [unfold KS2, TFIB_DEPOT; lia|]. split; [unfold KS2, TFIB_DEPOT; lia|].
  split; [intros o Ho; apply rw7; unfold KS2, TFIB_DEPOT; lia|].
  apply Forall_cons; [| apply Forall_nil].
  eapply (chunk_ok_val tfibsegs KE0 m0 KS2 0 4 (SLit 0) 0); [reflexivity | cbn; lia | cbn; lia | rewrite Z.add_0_r; exact VT]. }
apply Forall_nil.
Qed.
Lemma kPAIRS : pairwise_disjoint KE0 (R_DS :: KFIX).
Proof.
kz. apply pairwise_disjoint_of_extents. unfold R_DS, KFIX, D_consts, R_MAPk, R_NUQk, R_TABk, lit8, KNUQ, extent_of_region.
cbn [map app YP09.r_base YP09.r_lo YP09.r_hi base_val].
rewrite (KEr 2 2%bv eq_refl), KE37, unsigned_lit_small by (unfold KS2, TFIB_DEPOT; lia).
change (bv_unsigned (getr regs 2%bv)) with sp. unfold KS2, TFIB_DEPOT, d_map1, d_nuniq, DEP_STK.
cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
clear - Z1 Z8. repeat split; lia.
Qed.
Lemma kFACTS : forall E, kenvD E -> Forall (fun nf => afact_ok E (fst nf) (snd nf)) KF_fixed.
Proof.
intros E HE. kz. kfixu HE.
assert (W_ : forall k X, bv_unsigned (ew E k) = X -> ew E k = Z_to_bv 64 X)
  by (intros k X H; rewrite <- H; symmetry; apply Z_to_bv_bv_unsigned).
unfold KF_fixed, u64f.
apply Forall_cons.
{ apply (YD3a.AFo E 2%nat sp _ _ _ (W_ _ _ V2)); [pose proof (u64_range (getr regs 2%bv)); unfold spZ in *; lia
  | unfold kHighMemBeg, kHighMemEnd, DEP_STK; lia | change (2 ^ 4) with 16; exact Z9 | lia]. }
apply Forall_cons.
{ apply (YD3a.AFo E 10%nat buf _ _ _ (W_ _ _ V10)); [lia | unfold kHighMemBeg, kHighMemEnd; lia | change (2 ^ 3) with 8; exact Z10 | lia]. }
apply Forall_cons. { apply (YD3a.AFo E 11%nat _ _ _ _ (W_ _ _ V11)); [lia | lia | apply Z.mod_1_r | lia]. }
apply Forall_cons. { apply (YD3a.AFo E aHASH KHSH _ _ _ (W_ _ _ V36)); [lia | lia | apply Z.mod_1_r | lia]. }
apply Forall_cons.
{ apply (YD3a.AFo E aS2 KS2 _ _ _ (W_ _ _ V37)); unfold KS2, TFIB_DEPOT; [lia | lia | | lia].
  change (2 ^ 2) with 4. apply Z.mod_divide; [lia|]. exists (395702 + Kbkt). lia. }
apply Forall_nil.
Qed.
Lemma kSEED : st_ok tfibsegs KE0 SS_K0 (restrict Hd (mkst regs (Z_to_bv 64 A_StackDepotPut) mem (seg_rom tfibsegs))).
Proof.
rewrite restrict_mkst_fx. unfold SS_K0. apply (entry_st_ok_full tfibsegs).
- apply regs_ok_Ereg.
- vm_compute. reflexivity.
- exact kREG0.
- exact kPAIRS.
- split; [| split; exact I]. apply YFem.atoms_ok_of_Forall. apply (kFACTS KE0 kenvD_E0).
Qed.

(* ---- the frame: writes stay in KWIN ---- *)
Definition KWIN (a : Z) : Prop := (sp - DEP_STK <= a < sp) \/ (KS2 <= a < KS2 + 4) \/ (KNUQ <= a < KNUQ + 4).
Definition KINV (m : word -> option byte) : Prop :=
  (forall x : word, ~ KWIN (bv_unsigned x) -> m x = mem x) /\ mem_grows (mrestrict Hd mem) (mrestrict Hd m).
Lemma KINV_mem : KINV mem.
Proof. split; [intros x _; reflexivity | intros a Ha; exact Ha]. Qed.
Lemma KINV_run : forall E rs (m m' : word -> option byte),
  KINV m -> kenvD E -> kwsk_ok rs = true -> frame_of E rs m m' -> mem_grows (mrestrict Hd m) (mrestrict Hd m') -> KINV m'.
Proof.
intros E rs m m' [IF IP] HE Hb HF HG. split.
- intros x Hx. rewrite (HF x). { exact (IF x Hx). } intros Hw.
  destruct (in_wrange_windows E rs _ Hw) as (b & lo & hi & Hin & Hr).
  pose proof (proj1 (forallb_forall _ _) Hb _ Hin) as Ht. cbn beta in Ht. apply Bool.orb_prop in Ht as [Ht|Ht].
  2:{ cbn [fst snd] in Ht. apply Z.leb_le in Ht. clear - Hr Ht. lia. }
  apply Hx. kfixu HE. unfold KWSK in Ht. cbn [existsb] in Ht. unfold KWIN.
  repeat (apply Bool.orb_prop in Ht as [Ht|Ht]);
  try (apply win_eqb_eq in Ht; injection Ht as -> -> ->; cbn [fst snd base_val] in Hr).
  + rewrite V2 in Hr. clear - Hr. lia.
  + rewrite V37 in Hr. clear - Hr. lia.
  + clear - Hr. lia.
  + discriminate Ht.
- exact (mem_grows_trans' _ _ _ IP HG).
Qed.
Lemma kbuf_outside : forall q, 0 <= q < 240 -> ~ KWIN (buf + q).
Proof. intros q Hq Hw. kz. unfold KWIN, KS2, KNUQ, TFIB_DEPOT, d_nuniq, DEP_STK in Hw. clear - Hq Hw Z1 Z3 Z5 Z8. lia. Qed.
Lemma kwords_INV : forall m, KINV m -> forall i, (i < length tr)%nat ->
  val_mem tfibsegs (mrestrict Hd m) (buf + 8 * Z.of_nat i) 8 (nth i tr 0).
Proof.
intros m [IF _] i Hi. kz. eapply (val_mem_frame Hd mem m); [| exact (Hwords i Hi)].
intros k Hk. apply IF. rewrite unsigned_lit_small by (clear - Hi Hk Z3 Z4 Z6; lia).
replace (buf + 8 * Z.of_nat i + Z.of_nat k) with (buf + (8 * Z.of_nat i + Z.of_nat k)) by lia.
apply kbuf_outside. clear - Hi Hk Z6. lia.
Qed.
Lemma kwords_mod_INV : forall m, KINV m -> forall i, (i < length tr)%nat ->
  val_mem tfibsegs (mrestrict Hd m) (buf + 8 * Z.of_nat i) 8 ((nth i tr 0) mod 2 ^ 64).
Proof. intros m HI i Hi. apply kval_mem_mod64. exact (kwords_INV m HI i Hi). Qed.
Ltac kinv_step HI HE INVn :=
  lazymatch goal with
  | HF : frame_of ?E ?rs ?mold (ms_mem ?msA), HG : mem_grows _ _ |- _ =>
    assert (INVn : KINV (ms_mem msA)) by (apply (KINV_run E rs _ _ HI HE ltac:(vm_compute; reflexivity) HF HG)); clear HF HG HI
  end.

(* ---- the hash loop (YFem's reabs_H / hash_loop) ---- *)
Lemma khacc_u64 : forall i, 0 <= YFem.hacc tr i < 2 ^ 64.
Proof.
intros i. unfold YFem.hacc. apply YFem.fold_dh_u64. unfold YFem.H0v.
apply lxor_u64; [apply Z.mod_pos_bound; lia | unfold DH_SEED; lia].
Qed.
Lemma kfirstn_S_nth : forall (l : list Z) i, (i < length l)%nat -> firstn (Datatypes.S i) l = firstn i l ++ [nth i l 0].
Proof.
induction l as [|x l IH]; intros i Hi; cbn in Hi; [lia|].
destruct i as [|i]; [reflexivity|]. cbn [firstn nth app]. rewrite (IH i) by lia. reflexivity.
Qed.
Lemma khacc_S : forall i, (i < length tr)%nat -> YFem.hacc tr (Datatypes.S i) = dh_step (YFem.hacc tr i) (nth i tr 0).
Proof. intros i Hi. unfold YFem.hacc. rewrite (kfirstn_S_nth tr i Hi), fold_left_app. reflexivity. Qed.
Definition KEH (E : env) (i : nat) (rg : bvmap 5 word) : env :=
  havoc E 42 [Z_to_bv 64 ((nth i tr 0) mod 2 ^ 64); Z_to_bv 64 (YFem.hacc tr i); Z_to_bv 64 (buf + 8 * Z.of_nat i);
              Z_to_bv 64 (buf + 8 * Z.of_nat (length tr)); getr rg 15%bv; getr rg 16%bv].
Lemma kRW_disj : forall E i, kenvD E -> (i < length tr)%nat -> bv_unsigned (ew E dP) = buf + 8 * Z.of_nat i ->
  all_disjoint E R_W KFIX'.
Proof.
intros E i HE Hi HP. kz. kfixu HE.
apply all_disjoint_of_extents.
unfold KFIX', KFIX, D_consts, R_W, KR_DS', R_MAPk, R_NUQk, R_TABk, lit8, KNUQ, extent_of_region.
cbn [map app YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite HP, V2, V37.
unfold KS2, TFIB_DEPOT, d_map1, d_nuniq. cbn [zall_disjoint]. unfold zdisj. cbn [fst snd].
clear - Z1 Z2 Z3 Z4 Z5 Z6 Z8 Hi. repeat split; lia.
Qed.
Lemma kreabs_H : forall E ss ms i,
  st_ok tfibsegs E ss (restrict Hd ms) -> kenvD E -> ss_pc ss = A_HLOOP ->
  reabs_check YFem.LT42 ss KHREGS KHF = true -> submem KFIX' (ss_mem ss) -> (i < length tr)%nat ->
  getr (ms_regs ms) 11%bv = Z_to_bv 64 (buf + 8 * Z.of_nat i) -> getr (ms_regs ms) 12%bv = Z_to_bv 64 (YFem.hacc tr i) ->
  getr (ms_regs ms) 14%bv = Z_to_bv 64 (buf + 8 * Z.of_nat (length tr)) -> KINV (ms_mem ms) ->
  let E' := KEH E i (ms_regs ms) in
  st_ok tfibsegs E' S_KH (restrict Hd ms) /\ kenvD E' /\
  ew E' dW = Z_to_bv 64 ((nth i tr 0) mod 2 ^ 64) /\ ew E' dH = Z_to_bv 64 (YFem.hacc tr i) /\
  ew E' dP = Z_to_bv 64 (buf + 8 * Z.of_nat i) /\ ew E' dE = Z_to_bv 64 (buf + 8 * Z.of_nat (length tr)).
Proof.
intros E ss ms i HS HE Hpc Hck Hsub Hi G11 G12 G14 HI. kz. cbn zeta. set (E' := KEH E i (ms_regs ms)).
assert (HE' : kenvD E') by (apply kenvD_havoc; [exact HE | unfold K_D; lia]).
assert (EW : ew E' dW = Z_to_bv 64 ((nth i tr 0) mod 2 ^ 64)) by reflexivity.
assert (EHh : ew E' dH = Z_to_bv 64 (YFem.hacc tr i)) by reflexivity.
assert (EP : ew E' dP = Z_to_bv 64 (buf + 8 * Z.of_nat i)) by reflexivity.
assert (EE : ew E' dE = Z_to_bv 64 (buf + 8 * Z.of_nat (length tr))) by reflexivity.
pose proof (Z.mod_pos_bound (nth i tr 0) (2 ^ 64) ltac:(lia)) as WR. pose proof (khacc_u64 i) as HR.
assert (UP : bv_unsigned (ew E' dP) = buf + 8 * Z.of_nat i) by (rewrite EP; apply unsigned_lit_small; clear - Hi Z3 Z4 Z6; lia).
split; [| split; [exact HE' | split; [exact EW | split; [exact EHh | split; [exact EP | exact EE]]]]].
unfold S_KH. rewrite <- Hpc.
apply (st_ok_add_region E' (mkSS (ss_pc ss) KHREGS KFIX' None KHF) (restrict Hd ms) R_W).
- apply (st_ok_reabs tfibsegs YFem.LT42 E E' ss (restrict Hd ms) KHREGS KFIX' KHF HS (kagree_pd_havoc E 42 _ ltac:(lia)) Hck).
  + cbn [ms_regs restrict]. apply Forall_forall. intros [r j] Hin. vm_compute in Hin. cbn [fst snd].
    destruct Hin as [H | [H | [H | [H | [H | []]]]]]; injection H as <- <-.
    * apply (YFem.OBr E' _ _ 11%bv 44%nat _ EP G11). vm_compute; reflexivity.
    * apply (YFem.OBr E' _ _ 12%bv 43%nat _ EHh G12). vm_compute; reflexivity.
    * apply (YFem.OBr E' _ _ 14%bv 45%nat _ EE G14). vm_compute; reflexivity.
    * apply (YFem.OBr E' _ _ 15%bv 46%nat (getr (ms_regs ms) 15%bv) eq_refl eq_refl). vm_compute; reflexivity.
    * apply (YFem.OBr E' _ _ 16%bv 47%nat (getr (ms_regs ms) 16%bv) eq_refl eq_refl). vm_compute; reflexivity.
  + assert (FO : fact_obls YFem.LT42 KHF = [(dW, u64f); (dH, u64f); (dP, mkAF kHighMemBeg (kHighMemEnd - 8) 3);
      (dE, mkAF kHighMemBeg kHighMemEnd 3); (46%nat, u64f); (47%nat, u64f)]) by (clear; vm_compute; reflexivity).
    rewrite FO. clear FO.
    apply Forall_cons; [apply (kJKf E' _ _ EW)|]. apply Forall_cons; [apply (kJKf E' _ _ EHh)|].
    apply Forall_cons.
    { cbn [fst snd]. apply (YD3a.AFo E' dP _ _ _ _ EP); clear - Hi Z3 Z4 Z6 Z10; [lia | unfold kHighMemBeg, kHighMemEnd; lia | | lia].
      change (2 ^ 3) with 8. apply Z.mod_divide in Z10 as [q Hq]; [|lia]. rewrite Hq. apply Z.mod_divide; [lia|].
      exists (q + Z.of_nat i). lia. }
    apply Forall_cons.
    { cbn [fst snd]. apply (YD3a.AFo E' dE _ _ _ _ EE); clear - Z3 Z4 Z6 Z10; [lia | unfold kHighMemBeg, kHighMemEnd; lia | | lia].
      change (2 ^ 3) with 8. apply Z.mod_divide in Z10 as [q Hq]; [|lia]. rewrite Hq. apply Z.mod_divide; [lia|].
      exists (q + Z.of_nat (length tr)). lia. }
    apply Forall_cons; [apply (kJKf E' _ (getr (ms_regs ms) 15%bv)); reflexivity|].
    apply Forall_cons; [apply (kJKf E' _ (getr (ms_regs ms) 16%bv)); reflexivity|]. apply Forall_nil.
  + cbn [ms_mem restrict]. apply (YFem.sub_mem_ok E E' ss); [exact (st_ok_mem_ok tfibsegs E ss _ HS) | exact Hsub
    | vm_compute; reflexivity | vm_compute; reflexivity | | reflexivity].
    intros n Hn. subst E'. unfold KEH. rewrite ew_havoc_old by lia. reflexivity.
- vm_compute. reflexivity.
- cbn [ms_mem restrict]. unfold region_ok, R_W. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
  rewrite UP. split; [clear - Z3; lia|]. split; [clear - Hi Z4 Z6; lia|]. split; [intros o Ho; exfalso; clear - Ho; lia|].
  apply Forall_cons; [| apply Forall_nil].
  eapply (chunk_ok_val tfibsegs E' _ _ 0 8 (SOff dW 0) ((nth i tr 0) mod 2 ^ 64));
    [cbn [sv_denot]; rewrite EW, unsigned_lit_small by exact WR; f_equal; lia | exact WR | cbn; lia |].
  rewrite Z.add_0_r. exact (kwords_mod_INV _ HI i Hi).
- cbn [ss_mem]. exact (kRW_disj E' i HE' Hi UP).
Qed.

(* ---- after the loop: 0x71010 (tab[b1] = 0) -> beqz -> lock (tab[b1] := 0x80000000, old 0) -> beq -> amoadd.w
   n_uniq_ids 0 -> 1 -> map1_[0] = 0 -> jal Create; the run stops at Create's entry 0x71714 ---- *)
Lemma kpost : forall E ss ms mat, st_ok tfibsegs E ss (restrict Hd ms) -> kenvD E -> KINV (ms_mem ms) -> ss = S_KP ->
  SRr tfibsegs W (mkCfg ms (with_vm_backing (m_vm_lazy md) mat md)) Q.
Proof.
intros E ss ms mat HS HE HI ->. pose proof Hwx_tfa as HWX. kz. kfixu HE.
pose proof (ts_depot B HB) as ED.
assert (EQS2 : TFIB_DEPOT + 4 * ((YF0p.tfib_dhash tr mod 2 ^ 64) mod d_tab_words) = KS2).
{ unfold KS2, Kbkt, KHSH. rewrite (Z.mod_small (YF0p.tfib_dhash tr) (2 ^ 64)) by exact (YFem.tfib_dhash_u64 tr). reflexivity. }
assert (EG : forall (k : nat) (r : bv 5), (k < 32)%nat -> Z.of_nat k = bv_unsigned r -> ew E k = getr regs r).
{ intros k r Hk Hr. rewrite (HE k ltac:(unfold K_D; lia)). exact (KEr k r Hr). }
srr_run_to_shG tfibtbl_rtD_ok HS 0x7243c. kinv_step HI HE INV1.
rewrite (st_ok_restrict_mkst tfibsegs (w_H W) E _ _ HS eq_refl). apply K.
unfold at_create_call. cbv zeta. rewrite ED, EQS2.
split. { rregk HS (1%bv : bv 5) G. rewrite G. reflexivity. }
split. { rregk HS (2%bv : bv 5) G. rewrite G. apply bv_eq. rewrite denot_SOff, V2, unsigned_lit_small by lia.
  unfold zcanon, M64. rewrite Z.mod_small by lia. lia. }
split. { rregk HS (10%bv : bv 5) G. rewrite G. reflexivity. }
split. { rregk HS (11%bv : bv 5) G. rewrite G. reflexivity. }
split. { rregk HS (8%bv : bv 5) G. rewrite G. reflexivity. }
split. { rregk HS (9%bv : bv 5) G. rewrite G. reflexivity. }
split.
{ unfold put_cs. cbv zeta. rewrite ED, EQS2.
  split. { rregk HS (18%bv : bv 5) G. rewrite G, soff0, (HE 37%nat ltac:(unfold K_D; lia)). exact KE37. }
  split. { rregk HS (19%bv : bv 5) G. rewrite G, soff0, (HE 36%nat ltac:(unfold K_D; lia)). exact KE36. }
  split. { rregk HS (20%bv : bv 5) G. rewrite G. reflexivity. }
  split. { rregk HS (21%bv : bv 5) G. rewrite G. reflexivity. }
  split. { rregk HS (22%bv : bv 5) G. rewrite G. reflexivity. }
  split. { rregk HS (23%bv : bv 5) G. rewrite G. reflexivity. }
  split. { rregk HS (24%bv : bv 5) G. rewrite G. reflexivity. }
  split. { rregk HS (25%bv : bv 5) G. rewrite G. reflexivity. }
  split. { rregk HS (3%bv : bv 5) G. rewrite G, soff0. exact (EG 3%nat 3%bv ltac:(lia) eq_refl). }
  split. { rregk HS (4%bv : bv 5) G. rewrite G, soff0. exact (EG 4%nat 4%bv ltac:(lia) eq_refl). }
  split. { rregk HS (26%bv : bv 5) G. rewrite G, soff0. exact (EG 26%nat 26%bv ltac:(lia) eq_refl). }
  rregk HS (27%bv : bv 5) G. rewrite G, soff0. exact (EG 27%nat 27%bv ltac:(lia) eq_refl). }
split.
{ unfold put_frame, put_saved. cbv zeta.
  repeat split.
  - memv HS 1%nat 17%nat; [rewrite V2; lia | rewrite soff0, (EG 1%nat 1%bv ltac:(lia) eq_refl), Z_to_bv_bv_unsigned; reflexivity | apply u64_range].
  - memv HS 1%nat 16%nat; [rewrite V2; lia | rewrite soff0, (EG 8%nat 8%bv ltac:(lia) eq_refl), Z_to_bv_bv_unsigned; reflexivity | apply u64_range].
  - memv HS 1%nat 15%nat; [rewrite V2; lia | rewrite soff0, (EG 9%nat 9%bv ltac:(lia) eq_refl), Z_to_bv_bv_unsigned; reflexivity | apply u64_range].
  - memv HS 1%nat 14%nat; [rewrite V2; lia | rewrite soff0, (EG 18%nat 18%bv ltac:(lia) eq_refl), Z_to_bv_bv_unsigned; reflexivity | apply u64_range].
  - memv HS 1%nat 13%nat; [rewrite V2; lia | rewrite soff0, (EG 19%nat 19%bv ltac:(lia) eq_refl), Z_to_bv_bv_unsigned; reflexivity | apply u64_range].
  - memv HS 1%nat 12%nat; [rewrite V2; lia | rewrite soff0, (EG 20%nat 20%bv ltac:(lia) eq_refl), Z_to_bv_bv_unsigned; reflexivity | apply u64_range].
  - memv HS 1%nat 11%nat; [rewrite V2; lia | rewrite soff0, (EG 21%nat 21%bv ltac:(lia) eq_refl), Z_to_bv_bv_unsigned; reflexivity | apply u64_range].
  - memv HS 1%nat 10%nat; [rewrite V2; lia | rewrite soff0, (EG 22%nat 22%bv ltac:(lia) eq_refl), Z_to_bv_bv_unsigned; reflexivity | apply u64_range].
  - memv HS 1%nat 9%nat; [rewrite V2; lia | rewrite soff0, (EG 23%nat 23%bv ltac:(lia) eq_refl), Z_to_bv_bv_unsigned; reflexivity | apply u64_range].
  - memv HS 1%nat 8%nat; [rewrite V2; lia | rewrite soff0, (EG 24%nat 24%bv ltac:(lia) eq_refl), Z_to_bv_bv_unsigned; reflexivity | apply u64_range].
  - memv HS 1%nat 7%nat; [rewrite V2; lia | rewrite soff0, (EG 25%nat 25%bv ltac:(lia) eq_refl), Z_to_bv_bv_unsigned; reflexivity | apply u64_range].
  - memv HS 1%nat 6%nat; [rewrite V2; lia | rewrite soff0, (EG 10%nat 10%bv ltac:(lia) eq_refl); exact R10 | lia].
  - memv HS 1%nat 5%nat; [rewrite V2; lia | rewrite soff0, (EG 11%nat 11%bv ltac:(lia) eq_refl); exact R11 | lia]. }
split.
{ (* tab[b1]: the 4-byte chunk holds the sign-extended word 0xffffffff80000000 (sc.w writes its low half) *)
  pose proof (YN0d.st_ok_chunk tfibsegs E _ _ 7%nat _ _ HS eq_refl (or_introl eq_refl)) as C.
  unfold YP09.chunk_ok in C. cbn [YP09.c_off YP09.c_val c_len cv_len base_val YP09.r_base ms_mem restrict] in C.
  intros k Hk. destruct (C (Z.of_nat k) ltac:(cbn; lia)) as (b & Hb1 & Hb2).
  cbn [cbyte sv_denot] in Hb1. injection Hb1 as <-. rewrite V37', Z.add_0_r in Hb2. rewrite Hb2. f_equal.
  destruct k as [|[|[|[|k]]]]; [apply bv_eq; vm_compute; reflexivity | apply bv_eq; vm_compute; reflexivity
    | apply bv_eq; vm_compute; reflexivity | apply bv_eq; vm_compute; reflexivity | lia]. }
split. { memv HS 6%nat 0%nat; [unfold TFIB_DEPOT, d_nuniq; lia | reflexivity | lia]. }
split. { intros i Hi. exact (kwords_INV _ INV1 i Hi). }
split. { intros a N1 N2 N3. apply (proj1 INV1). unfold KWIN, KNUQ. tauto. }
intros a Pa. exact (apresent_grows Hd mem _ a (proj2 INV1) Pa).
Qed.

Lemma khash_loop : forall k i E ms mat,
  (length tr - i <= k)%nat -> (i < length tr)%nat ->
  st_ok tfibsegs E S_KH (restrict Hd ms) -> kenvD E -> KINV (ms_mem ms) ->
  ew E dW = Z_to_bv 64 ((nth i tr 0) mod 2 ^ 64) -> ew E dH = Z_to_bv 64 (YFem.hacc tr i) ->
  ew E dP = Z_to_bv 64 (buf + 8 * Z.of_nat i) -> ew E dE = Z_to_bv 64 (buf + 8 * Z.of_nat (length tr)) ->
  SRr tfibsegs W (mkCfg ms (with_vm_backing (m_vm_lazy md) mat md)) Q.
Proof.
induction k as [|k IH]; intros i E ms mat Hk Hi HS HE HI EW EHh EP EE; [exfalso; clear - Hk Hi; lia|].
pose proof Hwx_tfa as HWX. kz.
pose proof (Z.mod_pos_bound (nth i tr 0) (2 ^ 64) ltac:(lia)) as WR. pose proof (khacc_u64 i) as HR.
assert (UW : bv_unsigned (ew E dW) = (nth i tr 0) mod 2 ^ 64) by (rewrite EW; apply unsigned_lit_small; exact WR).
assert (UH : bv_unsigned (ew E dH) = YFem.hacc tr i) by (rewrite EHh; apply unsigned_lit_small; exact HR).
assert (UP : bv_unsigned (ew E dP) = buf + 8 * Z.of_nat i) by (rewrite EP; apply unsigned_lit_small; clear - Hi Z3 Z4 Z6; lia).
assert (UE : bv_unsigned (ew E dE) = buf + 8 * Z.of_nat (length tr)) by (rewrite EE; apply unsigned_lit_small; clear - Z3 Z4 Z6; lia).
unfold dW in UW. unfold dH in UH. unfold dP in UP. unfold dE in UE.
srr_runG tfibtbl_rtD_ok HS. kinv_step HI HE INV1.
srr_branch_with tfibtbl_rtD_ok HS.
- apply (YFem.condZ E BC_NE 44 8 45 0 true) in Hc; [| rewrite UP; clear - Hi Z3 Z4 Z6; lia | rewrite UE; clear - Z3 Z4 Z6; lia].
  cbn beta iota in Hc. rewrite UP, UE, Z.add_0_r in Hc. apply Bool.negb_true_iff in Hc. apply Z.eqb_neq in Hc.
  assert (Hi' : (Datatypes.S i < length tr)%nat) by (clear - Hc Hi; lia).
  srr_runG tfibtbl_rtD_ok HS. kinv_step INV1 HE INV2.
  rreg HS (11%bv : bv 5) G11. rewrite UP in G11.
  pose proof (st_ok_reg_denot Hd E _ _ 12%bv HS) as G12. cbn [ms_regs restrict] in G12.
  lazymatch type of G12 with _ = sv_denot E ?e => replace e with X_STEP in G12 by reflexivity end.
  rewrite (YFem.denot_of_U E X_STEP _ (step_val E (YFem.hacc tr i) _ UW UH WR HR)) in G12.
  rewrite kdh_step_mod, <- (khacc_S i Hi) in G12.
  rreg HS (14%bv : bv 5) G14.
  lazymatch type of HS with st_ok _ _ ?ss2 (restrict _ ?ms2) =>
    destruct (kreabs_H E ss2 ms2 (Datatypes.S i) HS HE eq_refl ltac:(vm_compute; reflexivity)
      ltac:(cbn [ss_mem]; repeat (apply submem_refl || apply submem_drop)) Hi'
      ltac:(rewrite G11; f_equal; lia) G12 ltac:(rewrite G14; exact EE) INV2)
    as (HS' & HE' & EW' & EH' & EP' & EE')
  end.
  lazymatch type of HS' with st_ok _ ?E' _ (restrict _ ?ms2) =>
    apply (IH (Datatypes.S i) E' ms2 _ ltac:(clear - Hk Hi'; lia) Hi' HS' HE' INV2 EW' EH' EP' EE') end.
- apply (YFem.condZ E BC_NE 44 8 45 0 false) in Hc; [| rewrite UP; clear - Hi Z3 Z4 Z6; lia | rewrite UE; clear - Z3 Z4 Z6; lia].
  cbn beta iota in Hc. rewrite UP, UE, Z.add_0_r in Hc. apply Bool.negb_false_iff in Hc. apply Z.eqb_eq in Hc.
  assert (Hn : Datatypes.S i = length tr) by (clear - Hc Hi; lia).
  srr_runG tfibtbl_rtD_ok HS. kinv_step INV1 HE INV3.
  assert (FIN : U E X_FIN = KHSH).
  { rewrite (fin_val E (YFem.hacc tr i) _ UW UH WR HR), kdh_step_mod, <- (khacc_S i Hi), Hn. exact (YFem.hacc_full tr). }
  kfixu HE.
  apply (st_ok_pin_regU E _ _ 19%bv (SOff aHASH 0)) in HS; [| intros X; discriminate |].
  2:{ lazymatch goal with |- _ = U E ?e => replace e with X_FIN by reflexivity end. rewrite FIN, U_SOff, V36.
      unfold zcanon, M64. rewrite Z.add_0_r. rewrite Z.mod_small by exact Z7. reflexivity. }
  apply (st_ok_pin_regU E _ _ 18%bv (SOff aS2 0)) in HS; [| intros X; discriminate |].
  2:{ lazymatch goal with |- _ = U E ?e => replace e with X_S2 by reflexivity end. rewrite s2_of_fin, FIN, U_SOff, V37.
      unfold zcanon, M64, KS2, Kbkt, d_tab_words. rewrite Z.add_0_r.
      rewrite Z.mod_small by (pose proof (Z.mod_pos_bound KHSH (2 ^ 20) ltac:(lia)); unfold TFIB_DEPOT; lia). reflexivity. }
  lazymatch type of HS with st_ok _ _ ?ssP (restrict _ ?msP) =>
    exact (kpost E ssP msP _ HS HE INV3 ltac:(vm_compute; reflexivity)) end.
Qed.

Lemma kentry : forall mat,
  SRr tfibsegs W (mkCfg (mkst regs (Z_to_bv 64 A_StackDepotPut) mem (seg_rom tfibsegs)) (with_vm_backing (m_vm_lazy md) mat md)) Q.
Proof.
intros mat. pose proof Hwx_tfa as HWX. kz. pose proof kSEED as HS. pose proof KINV_mem as HI. pose proof kenvD_E0 as HE. kfixu HE.
assert (E10 : ew KE0 10 = Z_to_bv 64 buf) by (rewrite <- R10; exact (KEr 10 10%bv eq_refl)).
srr_run_toG tfibtbl_rtD_ok HS A_HLOOP. kinv_step HI HE INV1.
apply (st_ok_pin_regU KE0 _ _ 13%bv (SLit 0)) in HS; [| intros X; discriminate |].
2:{ kred_sr. apply (pin_tag0 KE0 _ V11). clear - Z6; lia. }
rreg HS (11%bv : bv 5) G11. rewrite E10 in G11.
pose proof (st_ok_reg_denot Hd KE0 _ _ 12%bv HS) as G12. cbn [ms_regs restrict] in G12.
lazymatch type of G12 with _ = sv_denot _ ?e => rewrite (YFem.denot_of_U KE0 e _ (h0_val KE0 _ V11 ltac:(clear - Z6; lia))) in G12 end.
pose proof (st_ok_reg_denot Hd KE0 _ _ 14%bv HS) as G14. cbn [ms_regs restrict] in G14.
lazymatch type of G14 with _ = sv_denot _ ?e =>
  rewrite (YFem.denot_of_U KE0 e _ (end_val KE0 _ buf V11 ltac:(clear - Z6; lia) V10 ltac:(clear - Z3; lia) ltac:(clear - Z4 Z6; lia))) in G14 end.
lazymatch type of HS with st_ok _ _ ?ss1 (restrict _ ?ms1) =>
  destruct (kreabs_H KE0 ss1 ms1 0%nat HS kenvD_E0 eq_refl ltac:(vm_compute; reflexivity)
    ltac:(cbn [ss_mem]; repeat (apply submem_refl || apply submem_drop)) ltac:(clear - Z6; lia)
    ltac:(rewrite G11; f_equal; lia) ltac:(rewrite G12; reflexivity) G14 INV1) as (HS' & HE' & EW & EHh & EP & EE);
  apply (khash_loop (length tr) 0%nat _ ms1 _ ltac:(clear; lia) ltac:(clear - Z6; lia) HS' HE' INV1 EW EHh EP EE)
end.
Qed.

Lemma k1_main : SRr tfibsegs W (mkCfg (mkst regs (Z_to_bv 64 A_StackDepotPut) mem (seg_rom tfibsegs)) md) Q.
Proof. rewrite (same_but_materialized_wvb md md (same_but_materialized_refl md)). apply kentry. Qed.
End k1.

(* ===== K1: from StackDepotPut's entry to TwoLevelMap::Create's entry. Premises: the parts of YD3j's PRE the code
   reads (registers, trace words, stack, tr in the universe and non-empty, the empty depot's hash words, n_uniq_ids
   and map1_[0], and as_const for the three hash constants at 0x102d8 / 0x102f8 / 0x10398). ===== *)
Lemma put_to_create : forall (W : world tfibsegs) (regs : bvmap 5 word) (mem : word -> option byte) (md : Model)
    (ly : alayout) (buf : Z) (tr : list Z) (Q : world tfibsegs -> config -> Prop),
  let H := w_H W in let m := mrestrict H mem in let sp := spZ regs in let DP := as_depot B in
  getr regs 10 = Z_to_bv 64 buf -> getr regs 11 = Z_to_bv 64 (Z.of_nat (length tr)) -> YK0s.ret_ok (getr regs 1) ->
  (forall i, (i < length tr)%nat -> val_mem tfibsegs m (buf + 8 * Z.of_nat i) 8 (nth i tr 0)) ->
  buf mod 8 = 0 -> ly_stk_lo ly <= buf -> buf + 8 * 30 <= ly_stk_hi ly -> buf + 8 * 30 <= sp - DEP_STK \/ sp <= buf ->
  sp mod 16 = 0 -> kHighMemBeg <= ly_stk_lo ly -> ly_stk_hi ly <= kHighMemEnd ->
  ly_stk_lo ly <= sp - DEP_STK -> sp <= ly_stk_hi ly -> (forall a, sp - DEP_STK <= a < sp -> apresent H mem a) ->
  In tr (as_universe B) -> tr <> [] ->
  (forall b, 0 <= b < d_tab_words -> rd32 (aview tfibsegs H mem) (DP + 4 * b) 0) ->
  val_mem tfibsegs m (DP + d_nuniq) 4 0 -> val_mem tfibsegs m (DP + d_map1) 8 0 ->
  Forall (cell_holds B ly (aview tfibsegs H mem)) (as_const B ly) ->
  (forall regs1 mem1 mat, at_create_call regs H mem buf tr regs1 mem1 ->
     SRr tfibsegs W (mkCfg (mkst regs1 (Z_to_bv 64 tfib_A_TwoLevelMap_Create_71714) mem1 (seg_rom tfibsegs))
                           (with_vm_backing (m_vm_lazy md) mat md)) Q) ->
  SRr tfibsegs W (mkCfg (mkst regs (Z_to_bv 64 A_StackDepotPut) mem (seg_rom tfibsegs)) md) Q.
Proof.
intros W regs mem md ly buf tr Q. cbv zeta.
intros R10 R11 _ Hwords Hbuf8 Hbuflo Hbufhi Hbuf_sp Hsp16 Hstk0 Hstk1 Hsplo Hsphi P_stk Htr Hne HTAB HNUQ HMAP HCONST K.
eapply k1_main; eassumption.
Qed.

(* ===== K2: from Create's return 0x71190 (a0 = x) to Store's entry. Premises: K1's boundary registers (callee-saved
   part) with a0 = x, Put's frame, the stack window, and node 1's 16 bytes present, off the stack window and above the
   image (S7's P2-P4 give them). ===== *)
Lemma create_ret_to_store : forall (W : world tfibsegs) (regs0 regs : bvmap 5 word) (mem : word -> option byte)
    (md : Model) (buf x : Z) (tr : list Z) (Q : world tfibsegs -> config -> Prop),
  let H := w_H W in let sp := spZ regs0 in let P := sp - 112 in
  getr regs 2 = Z_to_bv 64 P -> getr regs 10 = Z_to_bv 64 x -> getr regs 8 = Z_to_bv 64 0 -> getr regs 9 = Z_to_bv 64 1 ->
  put_cs regs regs0 tr -> put_frame H mem regs0 buf tr ->
  sp mod 16 = 0 -> kHighMemBeg <= sp - DEP_STK -> sp <= kHighMemEnd -> (forall a, sp - DEP_STK <= a < sp -> apresent H mem a) ->
  in_app x kNodesBlockSize -> TFIB_IMG_END <= x -> (x + 32 <= sp - DEP_STK \/ sp <= x + 16) ->
  (forall i, 16 <= i < 32 -> apresent H mem (x + i)) ->
  (forall regs1 mem1 mat, at_store_call regs0 H mem buf tr x regs1 mem1 ->
     SRr tfibsegs W (mkCfg (mkst regs1 (Z_to_bv 64 tfib_A_StackStore_Store) mem1 (seg_rom tfibsegs))
                           (with_vm_backing (m_vm_lazy md) mat md)) Q) ->
  SRr tfibsegs W (mkCfg (mkst regs (Z_to_bv 64 0x71eb8) mem (seg_rom tfibsegs)) md) Q.
Proof.
intros W regs0 regs mem md buf x tr Q. cbv zeta.
intros R2 R10 R8 R9 CS PF Hsp16 Hsplo Hsphi Pstk XAPP XIMG XSTK XP K.
pose proof (ts_depot B HB) as ED. pose proof (ts_store B HB) as ES. pose proof Hwx_tfa as HWX.
pose proof (proj1 (@YG0f.ASAN_CEIL_range _)) as CEIL.
assert (SPR : 0 <= spZ regs0 < 2 ^ 64) by exact (u64_range (getr regs0 2%bv)).
pose proof (YFem.tfib_dhash_u64 tr) as HR.
pose proof CS as CS'. unfold put_cs in CS'. cbv zeta in CS'. rewrite ED in CS'.
destruct CS' as (C18 & C19 & C20 & C21 & C22 & C23 & C24 & C25 & C3 & C4 & C26 & C27).
assert (XR : 4096 <= x /\ x + kNodesBlockSize <= 0x7fffff800000)
  by (destruct XAPP as [XA1 [XA2 | [_ XA2]]]; unfold kLowShadowBeg in *; lia).
unfold kNodesBlockSize, kHighMemBeg, kHighMemEnd, DEP_STK, TFIB_IMG_END in *.
assert (ER : forall (k : nat) (r : bv 5), Z.of_nat k = bv_unsigned r -> ew (EK2 regs) k = getr regs r)
  by (intros k r Hk; exact (ew_Ereg_nat regs _ k r Hk)).
assert (U2 : bv_unsigned (ew (EK2 regs) 2) = spZ regs0 - 112).
{ rewrite (ER 2%nat 2%bv eq_refl), R2. apply unsigned_lit_small. lia. }
assert (U10 : bv_unsigned (ew (EK2 regs) 10) = x).
{ rewrite (ER 10%nat 10%bv eq_refl), R10. apply unsigned_lit_small. lia. }
(* the seed at 0x71190 *)
assert (HS : st_ok tfibsegs (EK2 regs) SS_K2 (restrict (w_H W) (mkst regs (Z_to_bv 64 0x71eb8) mem (seg_rom tfibsegs)))).
{ rewrite restrict_mkst_fx. unfold SS_K2. apply (entry_st_ok_full tfibsegs).
  all: try fold (EK2 regs).
  - apply regs_ok_pin; [| intros X; discriminate | cbn [sv_denot]; exact C22].
    apply regs_ok_pin; [apply regs_ok_Ereg | intros X; discriminate | cbn [sv_denot]; exact R9].
  - vm_compute. reflexivity.
  - apply Forall_cons.
    { apply (region_ok_stack tfibsegs (EK2 regs) _ 2 (spZ regs0 - 112) (-32)); [exact U2 | lia | lia |].
      intros a Ha. apply YD3a.apresent_wr. apply Pstk. lia. }
    apply Forall_cons.
    { apply (region_ok_window (EK2 regs) _ 10 x 16 24 16 24); [exact U10 | lia | lia |].
      intros a Ha. replace a with (x + (a - x)) by lia. apply YD3a.apresent_wr. apply XP. lia. }
    apply Forall_nil.
  - apply pairwise_disjoint_of_extents. unfold R_K2S, R_K2N. cbn [map]. rewrite !YD3a.ext_Some, U2, U10.
    cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd]. clear - XSTK. repeat split; lia.
  - split; [exact I | split; exact I]. }
srr_run_toG tfibtbl_rtD_ok HS 0x6f61c.
change (ss_mem SS_K2) with [R_K2S; R_K2N] in HF.
assert (FR : forall a, ~ (spZ regs0 - 144 <= a < spZ regs0 - 112) -> ~ (x + 16 <= a < x + 24) -> 0 <= a < 2 ^ 64 ->
  ms_mem ms (Z_to_bv 64 a) = mem (Z_to_bv 64 a)).
{ intros a N1 N2 Ha. apply HF. rewrite unsigned_lit_small by exact Ha. intros (r & Hin & Hr). cbn [In] in Hin.
  destruct Hin as [<-|[<-|[]]]; cbn [R_K2S R_K2N YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hr;
  [rewrite U2 in Hr; lia | rewrite U10 in Hr; lia]. }
assert (VF : forall a n v, spZ regs0 - 112 <= a -> a + Z.of_nat n <= spZ regs0 ->
  val_mem tfibsegs (mrestrict (w_H W) mem) a n v -> val_mem tfibsegs (mrestrict (w_H W) (ms_mem ms)) a n v).
{ intros a n v H1 H2 Hv. apply (val_mem_hframe (w_H W) (w_H W) mem (ms_mem ms)); [| exact Hv].
  intros k Hk. split; [reflexivity | apply FR; lia]. }
rewrite (st_ok_restrict_mkst tfibsegs (w_H W) (EK2 regs) _ _ HS eq_refl). apply K.
unfold at_store_call. cbv zeta. rewrite ES.
split. { rregk HS (1%bv : bv 5) G. rewrite G. reflexivity. }
split. { rregk HS (2%bv : bv 5) G. rewrite G. apply bv_eq. rewrite denot_SOff, U2, unsigned_lit_small by lia.
  unfold zcanon, M64. rewrite Z.mod_small by lia. lia. }
split. { rregk HS (10%bv : bv 5) G. rewrite G. reflexivity. }
split. { rregk HS (11%bv : bv 5) G. rewrite G. apply bv_eq. rewrite denot_SOff, U2, unsigned_lit_small by lia.
  unfold zcanon, M64. rewrite Z.mod_small by lia. lia. }
split. { rregk HS (12%bv : bv 5) G. rewrite G. apply bv_eq. rewrite denot_SOff, U2, unsigned_lit_small by lia.
  unfold zcanon, M64. rewrite Z.mod_small by lia. lia. }
split. { rregk HS (8%bv : bv 5) G. rewrite G. apply bv_eq. rewrite denot_SOff, U10, unsigned_lit_small by lia.
  unfold zcanon, M64. rewrite Z.mod_small by lia. lia. }
split. { rregk HS (9%bv : bv 5) G. rewrite G. apply bv_eq. rewrite denot_SOff, U10, unsigned_lit_small by lia.
  unfold zcanon, M64. rewrite Z.mod_small by lia. lia. }
split.
{ unfold put_cs. cbv zeta. rewrite ED.
  split. { rregk HS (18%bv : bv 5) G. rewrite G, soff0, (ER 18%nat 18%bv eq_refl). exact C18. }
  split. { rregk HS (19%bv : bv 5) G. rewrite G, soff0, (ER 19%nat 19%bv eq_refl). exact C19. }
  split. { rregk HS (20%bv : bv 5) G. rewrite G, soff0, (ER 20%nat 20%bv eq_refl). exact C20. }
  split. { rregk HS (21%bv : bv 5) G. rewrite G, soff0, (ER 21%nat 21%bv eq_refl). exact C21. }
  split. { rregk HS (22%bv : bv 5) G. rewrite G. reflexivity. }
  split. { rregk HS (23%bv : bv 5) G. rewrite G, soff0, (ER 23%nat 23%bv eq_refl). exact C23. }
  split. { rregk HS (24%bv : bv 5) G. rewrite G, soff0, (ER 24%nat 24%bv eq_refl). exact C24. }
  split. { rregk HS (25%bv : bv 5) G. rewrite G, soff0, (ER 25%nat 25%bv eq_refl). exact C25. }
  split. { rregk HS (3%bv : bv 5) G. rewrite G, soff0, (ER 3%nat 3%bv eq_refl). exact C3. }
  split. { rregk HS (4%bv : bv 5) G. rewrite G, soff0, (ER 4%nat 4%bv eq_refl). exact C4. }
  split. { rregk HS (26%bv : bv 5) G. rewrite G, soff0, (ER 26%nat 26%bv eq_refl). exact C26. }
  rregk HS (27%bv : bv 5) G. rewrite G, soff0, (ER 27%nat 27%bv eq_refl). exact C27. }
split. { memv HS 0%nat 2%nat; [rewrite U2; lia | reflexivity | lia]. }
split. { memv HS 0%nat 1%nat; [rewrite U2; lia | rewrite soff0, (ER 8%nat 8%bv eq_refl); exact R8 | lia]. }
split. { memv HS 0%nat 0%nat; [rewrite U2; lia | reflexivity | lia]. }
split.
{ unfold put_frame, put_saved in PF |- *. cbv zeta in PF |- *.
  destruct PF as ((S1 & S8 & S9 & S18 & S19 & S20 & S21 & S22 & S23 & S24 & S25) & SB & SN).
  repeat split; apply VF; try (cbn; lia); assumption. }
split. { memv HS 1%nat 0%nat; [rewrite U10; lia | rewrite soff0, (ER 19%nat 19%bv eq_refl); exact C19 | lia]. }
split.
{ intros a N1 N2. unfold DEP_STK in N1. apply HF. intros (r & Hin & Hr). cbn [In] in Hin.
  destruct Hin as [<-|[<-|[]]]; cbn [R_K2S R_K2N YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hr;
  [rewrite U2 in Hr; lia | rewrite U10 in Hr; lia]. }
intros a Pa. exact (apresent_grows (w_H W) mem (ms_mem ms) a HG Pa).
Qed.

(* ===== K3: from Store's return 0x70c34 (a0 = 1) to Put's return. Premises: K2's boundary registers (callee-saved
   part) and frames (StackDepotNode::store's ra, s0 and pack cell 0; Put's saved registers), node 1's link / store_id
   bytes present, off the stack window and above the image, and Put's entry ra a return address. ===== *)
Lemma store_ret_to_exit : forall (W : world tfibsegs) (regs0 regs : bvmap 5 word) (mem : word -> option byte)
    (md : Model) (x : Z) (tr : list Z) (Q : world tfibsegs -> config -> Prop),
  let H := w_H W in let m := mrestrict H mem in let sp := spZ regs0 in let P := sp - 112 in let N := P - 32 in
  getr regs 2 = Z_to_bv 64 N -> getr regs 10 = Z_to_bv 64 1 ->
  getr regs 8 = Z_to_bv 64 (x + 16) -> getr regs 9 = Z_to_bv 64 (x + 16) -> put_cs regs regs0 tr ->
  YK0s.ret_ok (getr regs0 1) ->
  val_mem tfibsegs m (N + 0x18) 8 0x71e40 -> val_mem tfibsegs m (N + 0x10) 8 0 -> val_mem tfibsegs m (N + 8) 8 0 ->
  put_saved H mem regs0 ->
  sp mod 16 = 0 -> kHighMemBeg <= sp - DEP_STK -> sp <= kHighMemEnd ->
  in_app x kNodesBlockSize -> TFIB_IMG_END <= x -> (x + 32 <= sp - DEP_STK \/ sp <= x + 16) ->
  (forall i, 24 <= i < 32 -> apresent H mem (x + i)) ->
  (forall regs1 mem1 mat, put_exit regs0 H mem tr x regs1 mem1 ->
     SRr tfibsegs W (mkCfg (mkst regs1 (getr regs0 1) mem1 (seg_rom tfibsegs)) (with_vm_backing (m_vm_lazy md) mat md)) Q) ->
  SRr tfibsegs W (mkCfg (mkst regs (Z_to_bv 64 0x7195c) mem (seg_rom tfibsegs)) md) Q.
Proof.
intros W regs0 regs mem md x tr Q. cbv zeta.
intros R2 R10 R8 R9 CS RA V18 V10 V08 PS Hsp16 Hsplo Hsphi XAPP XIMG XSTK XP K.
pose proof (ts_depot B HB) as ED. pose proof Hwx_tfa as HWX.
pose proof (proj1 (@YG0f.ASAN_CEIL_range _)) as CEIL.
assert (SPR : 0 <= spZ regs0 < 2 ^ 64) by exact (u64_range (getr regs0 2%bv)).
pose proof (YFem.tfib_dhash_u64 tr) as HR.
unfold put_cs in CS. cbv zeta in CS. rewrite ED in CS.
set (h := YF0p.tfib_dhash tr) in *. set (b1 := (h mod 2 ^ 64) mod d_tab_words) in *.
assert (BR : 0 <= b1 < 2 ^ 20) by (unfold b1, d_tab_words; apply Z.mod_pos_bound; lia).
destruct CS as (C18 & C19 & C20 & C21 & C22 & C23 & C24 & C25 & C3 & C4 & C26 & C27).
unfold put_saved in PS. cbv zeta in PS. destruct PS as (S1 & S8 & S9 & S18 & S19 & S20 & S21 & S22 & S23 & S24 & S25).
assert (XR : 4096 <= x /\ x + kNodesBlockSize <= 0x7fffff800000)
  by (destruct XAPP as [XA1 [XA2 | [_ XA2]]]; unfold kLowShadowBeg in *; lia).
unfold kNodesBlockSize, kHighMemBeg, kHighMemEnd, DEP_STK, TFIB_IMG_END in *.
assert (ER : forall (k : nat) (r : bv 5), Z.of_nat k = bv_unsigned r -> ew (EK3 regs regs0) k = getr regs r)
  by (intros k r Hk; exact (ew_Ereg_nat regs _ k r Hk)).
assert (U2 : bv_unsigned (ew (EK3 regs regs0) 2) = spZ regs0 - 144).
{ rewrite (ER 2%nat 2%bv eq_refl), R2, unsigned_lit_small by lia. lia. }
assert (U8 : bv_unsigned (ew (EK3 regs regs0) 8) = x + 16).
{ rewrite (ER 8%nat 8%bv eq_refl), R8. apply unsigned_lit_small. lia. }
assert (U18 : bv_unsigned (ew (EK3 regs regs0) 18) = TFIB_DEPOT + 4 * b1).
{ rewrite (ER 18%nat 18%bv eq_refl), C18. apply unsigned_lit_small. unfold TFIB_DEPOT. lia. }
(* the seed at 0x70c34 *)
assert (HS : st_ok tfibsegs (EK3 regs regs0) SS_K3 (restrict (w_H W) (mkst regs (Z_to_bv 64 0x7195c) mem (seg_rom tfibsegs)))).
{ rewrite restrict_mkst_fx. unfold SS_K3. apply (entry_st_ok_full tfibsegs).
  all: try fold (EK3 regs regs0).
  - apply regs_ok_pin; [apply regs_ok_Ereg | intros X; discriminate |].
    rewrite soff0, (ER 8%nat 8%bv eq_refl), R8, R9. reflexivity.
  - vm_compute. reflexivity.
  - apply Forall_cons.
    { apply (YD3a.region_ok_ro (EK3 regs regs0) _ 2 (spZ regs0 - 144)); [exact U2 | lia | lia |].
      assert (CS0 : forall o v, val_mem tfibsegs (mrestrict (w_H W) mem) (spZ regs0 - 144 + o) 8 v -> 0 <= v < 2 ^ 64 ->
        YP09.chunk_ok tfibsegs (EK3 regs regs0) (mrestrict (w_H W) mem) (spZ regs0 - 144) (ch8 o (SLit v))).
      { intros o v Hv Hr. apply (chunk_ok_val tfibsegs _ _ _ o 8 (SLit v) v); [reflexivity | exact Hr | cbn; lia | exact Hv]. }
      assert (CSr : forall o k (r : bv 5), val_mem tfibsegs (mrestrict (w_H W) mem) (spZ regs0 - 144 + o) 8 (bv_unsigned (getr regs0 r)) ->
        ew (EK3 regs regs0) k = getr regs0 r ->
        YP09.chunk_ok tfibsegs (EK3 regs regs0) (mrestrict (w_H W) mem) (spZ regs0 - 144) (ch8 o (SOff k 0))).
      { intros o k r Hv Hk. apply (chunk_ok_val tfibsegs _ _ _ o 8 (SOff k 0) (bv_unsigned (getr regs0 r)));
          [rewrite soff0, Hk; symmetry; apply Z_to_bv_bv_unsigned | apply u64_range | cbn; lia | exact Hv]. }
      repeat apply Forall_cons; try apply Forall_nil.
      + apply CS0; [replace (spZ regs0 - 144 + 8) with (spZ regs0 - 112 - 32 + 8) by lia; exact V08 | lia].
      + apply CS0; [replace (spZ regs0 - 144 + 16) with (spZ regs0 - 112 - 32 + 16) by lia; exact V10 | lia].
      + apply CS0; [replace (spZ regs0 - 144 + 24) with (spZ regs0 - 112 - 32 + 24) by lia; exact V18 | lia].
      + apply (CSr 56 42%nat 25%bv); [replace (spZ regs0 - 144 + 56) with (spZ regs0 - 112 + 24) by lia; exact S25 | reflexivity].
      + apply (CSr 64 41%nat 24%bv); [replace (spZ regs0 - 144 + 64) with (spZ regs0 - 112 + 32) by lia; exact S24 | reflexivity].
      + apply (CSr 72 40%nat 23%bv); [replace (spZ regs0 - 144 + 72) with (spZ regs0 - 112 + 40) by lia; exact S23 | reflexivity].
      + apply (CSr 80 39%nat 22%bv); [replace (spZ regs0 - 144 + 80) with (spZ regs0 - 112 + 48) by lia; exact S22 | reflexivity].
      + apply (CSr 88 38%nat 21%bv); [replace (spZ regs0 - 144 + 88) with (spZ regs0 - 112 + 56) by lia; exact S21 | reflexivity].
      + apply (CSr 96 37%nat 20%bv); [replace (spZ regs0 - 144 + 96) with (spZ regs0 - 112 + 64) by lia; exact S20 | reflexivity].
      + apply (CSr 104 36%nat 19%bv); [replace (spZ regs0 - 144 + 104) with (spZ regs0 - 112 + 72) by lia; exact S19 | reflexivity].
      + apply (CSr 112 35%nat 18%bv); [replace (spZ regs0 - 144 + 112) with (spZ regs0 - 112 + 80) by lia; exact S18 | reflexivity].
      + apply (CSr 120 34%nat 9%bv); [replace (spZ regs0 - 144 + 120) with (spZ regs0 - 112 + 88) by lia; exact S9 | reflexivity].
      + apply (CSr 128 33%nat 8%bv); [replace (spZ regs0 - 144 + 128) with (spZ regs0 - 112 + 96) by lia; exact S8 | reflexivity].
      + apply (CSr 136 32%nat 1%bv); [replace (spZ regs0 - 144 + 136) with (spZ regs0 - 112 + 104) by lia; exact S1 | reflexivity]. }
    apply Forall_cons.
    { apply (region_ok_window (EK3 regs regs0) _ 8 (x + 16) 8 16 8 16); [exact U8 | lia | lia |].
      intros a Ha. replace a with (x + (a - x)) by lia. apply YD3a.apresent_wr. apply XP. lia. }
    apply Forall_cons.
    { apply (region_ok_window (EK3 regs regs0) _ 18 (TFIB_DEPOT + 4 * b1) 0 4 0 4); [exact U18 | unfold TFIB_DEPOT; lia | unfold TFIB_DEPOT; lia |].
      intros a Ha. apply rw7. unfold TFIB_DEPOT in *. lia. }
    apply Forall_nil.
  - apply pairwise_disjoint_of_extents. unfold R_K3S, R_K3N, R_K3T. cbn [map]. rewrite !YD3a.ext_Some, U2, U8, U18.
    cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd]. unfold TFIB_DEPOT.
    clear - XSTK XIMG BR Hsplo XR. repeat split; lia.
  - split; [exact I | split; exact I]. }
srr_runG tfibtbl_rtD_ok HS.
change (ss_mem SS_K3) with [R_K3S; R_K3N; R_K3T] in HF.
rregk HS (1%bv : bv 5) G1. rewrite soff0 in G1. change (ew (EK3 regs regs0) 32) with (getr regs0 1%bv) in G1.
apply (SRr_bind tfibsegs W _ (fun W' c' => W' = W /\ exists mat', c' = mkCfg (mkst (ms_regs ms) (getr regs0 1%bv) (ms_mem ms)
  (seg_rom tfibsegs)) (with_vm_backing (m_vm_lazy md) mat' md)) Q).
{ eapply (SRr_ret_at tfibsegs tfibtbl_rtD tfibtbl_rtD_ok HWX W); [exact HS | reflexivity | vm_compute; reflexivity |].
  intros mat'. rewrite wvb_collapse. split; [reflexivity|]. exists mat'. rewrite G1. unfold YK0s.ret_ok in RA. rewrite RA. reflexivity. }
intros W' c' _ [-> [mat' ->]]. apply K.
unfold put_exit. cbv zeta. rewrite ED. change ((YF0p.tfib_dhash tr mod 2 ^ 64) mod d_tab_words) with b1.
split. { rregk HS (10%bv : bv 5) G. rewrite G, soff0, (ER 23%nat 23%bv eq_refl). exact C23. }
split.
{ apply regs_preserved_intro.
  - rregk HS (2%bv : bv 5) G. rewrite G. apply bv_eq. rewrite denot_SOff, U2. unfold zcanon, M64. rewrite Z.mod_small by lia. unfold spZ. lia.
  - rregk HS (3%bv : bv 5) G. rewrite G, soff0, (ER 3%nat 3%bv eq_refl). exact C3.
  - rregk HS (4%bv : bv 5) G. rewrite G, soff0, (ER 4%nat 4%bv eq_refl). exact C4.
  - rregk HS (8%bv : bv 5) G. rewrite G, soff0. reflexivity.
  - rregk HS (9%bv : bv 5) G. rewrite G, soff0. reflexivity.
  - rregk HS (18%bv : bv 5) G. rewrite G, soff0. reflexivity.
  - rregk HS (19%bv : bv 5) G. rewrite G, soff0. reflexivity.
  - rregk HS (20%bv : bv 5) G. rewrite G, soff0. reflexivity.
  - rregk HS (21%bv : bv 5) G. rewrite G, soff0. reflexivity.
  - rregk HS (22%bv : bv 5) G. rewrite G, soff0. reflexivity.
  - rregk HS (23%bv : bv 5) G. rewrite G, soff0. reflexivity.
  - rregk HS (24%bv : bv 5) G. rewrite G, soff0. reflexivity.
  - rregk HS (25%bv : bv 5) G. rewrite G, soff0. reflexivity.
  - rregk HS (26%bv : bv 5) G. rewrite G, soff0, (ER 26%nat 26%bv eq_refl). exact C26.
  - rregk HS (27%bv : bv 5) G. rewrite G, soff0, (ER 27%nat 27%bv eq_refl). exact C27. }
split. { memv HS 1%nat 1%nat; [rewrite U8; lia | rewrite soff0, (ER 10%nat 10%bv eq_refl); exact R10 | lia]. }
split. { memv HS 1%nat 0%nat; [rewrite U8; lia | rewrite soff0, (ER 21%nat 21%bv eq_refl); exact C21 | lia]. }
split. { memv HS 2%nat 0%nat; [rewrite U18; lia | rewrite soff0, (ER 23%nat 23%bv eq_refl); exact C23 | lia]. }
split.
{ intros a N1 N2. apply HF. intros (r & Hin & Hr). cbn [In] in Hin.
  destruct Hin as [<-|[<-|[<-|[]]]]; cbn [R_K3S R_K3N R_K3T YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hr;
  [lia | rewrite U8 in Hr; lia | rewrite U18 in Hr; lia]. }
intros a Pa. exact (apresent_grows (w_H W) mem (ms_mem ms) a HG Pa).
Qed.

(* ===== K0: the size-0 early return. StackDepotPut, Put's prologue (frame 0x70), s0 := a3 = 0 (beqz a3 skips the
   sb at 0x70f54), 0x70f58 sext.w a3, a2 = 0, a0 := 0, 0x70f60 beqz a3 -> 0x71134: restore ra, s0-s9, ret (a0 = 0).
   Premises: what the walk reads and writes (n = 0, ra a return address, Put's frame [sp - 112, sp) present). ===== *)
Lemma put_size0 : forall (W : world tfibsegs) (regs : bvmap 5 word) (mem : word -> option byte) (md : Model)
    (Q : world tfibsegs -> config -> Prop),
  let H := w_H W in let sp := spZ regs in
  getr regs 11 = Z_to_bv 64 0 -> YK0s.ret_ok (getr regs 1) -> 112 <= sp ->
  (forall a, sp - 112 <= a < sp -> apresent H mem a) ->
  (forall regs1 mem1 mat, getr regs1 10 = Z_to_bv 64 0 -> regs_preserved regs regs1 ->
     (forall x : word, ~ (sp - 112 <= bv_unsigned x < sp) -> mem1 x = mem x) ->
     (forall a, apresent H mem a -> apresent H mem1 a) ->
     SRr tfibsegs W (mkCfg (mkst regs1 (getr regs 1) mem1 (seg_rom tfibsegs)) (with_vm_backing (m_vm_lazy md) mat md)) Q) ->
  SRr tfibsegs W (mkCfg (mkst regs (Z_to_bv 64 A_StackDepotPut) mem (seg_rom tfibsegs)) md) Q.
Proof.
intros W regs mem md Q. cbv zeta. intros R11 RA SPL P_stk K. pose proof Hwx_tfa as HWX.
assert (SPR : 0 <= spZ regs < 2 ^ 64) by exact (u64_range (getr regs 2%bv)).
assert (ER : forall (k : nat) (r : bv 5), Z.of_nat k = bv_unsigned r -> ew (EK2 regs) k = getr regs r)
  by (intros k r Hk; exact (ew_Ereg_nat regs _ k r Hk)).
assert (U2 : bv_unsigned (ew (EK2 regs) 2) = spZ regs) by (rewrite (ER 2%nat 2%bv eq_refl); reflexivity).
assert (HS : st_ok tfibsegs (EK2 regs) SS_Z0 (restrict (w_H W) (mkst regs (Z_to_bv 64 A_StackDepotPut) mem (seg_rom tfibsegs)))).
{ rewrite restrict_mkst_fx. unfold SS_Z0. apply (entry_st_ok_full tfibsegs).
  all: try fold (EK2 regs).
  - apply regs_ok_pin; [apply regs_ok_Ereg | intros X; discriminate | cbn [sv_denot]; exact R11].
  - vm_compute. reflexivity.
  - apply Forall_cons; [| apply Forall_nil].
    apply (region_ok_stack tfibsegs (EK2 regs) _ 2 (spZ regs) (-112)); [exact U2 | lia | lia |].
    intros a Ha. apply YD3a.apresent_wr. apply P_stk. lia.
  - apply pairwise_disjoint_of_extents. cbn. tauto.
  - split; [exact I | split; exact I]. }
srr_runG tfibtbl_rtD_ok HS.
change (ss_mem SS_Z0) with [R_Z0] in HF.
rregk HS (1%bv : bv 5) G1. rewrite soff0, (ER 1%nat 1%bv eq_refl) in G1.
apply (SRr_bind tfibsegs W _ (fun W' c' => W' = W /\ exists mat', c' = mkCfg (mkst (ms_regs ms) (getr regs 1%bv) (ms_mem ms)
  (seg_rom tfibsegs)) (with_vm_backing (m_vm_lazy md) mat' md)) Q).
{ eapply (SRr_ret_at tfibsegs tfibtbl_rtD tfibtbl_rtD_ok HWX W); [exact HS | reflexivity | vm_compute; reflexivity |].
  intros mat'. rewrite wvb_collapse. split; [reflexivity|]. exists mat'. rewrite G1. unfold YK0s.ret_ok in RA. rewrite RA. reflexivity. }
intros W' c' _ [-> [mat' ->]]. apply K.
- rregk HS (10%bv : bv 5) G. rewrite G. reflexivity.
- apply regs_preserved_intro.
  all: match goal with |- getr _ ?r = _ => let G := fresh "G" in rregk HS r G; rewrite G, soff0; apply ER; reflexivity end.
- intros x N1. apply HF. intros (r & Hin & Hr). cbn [In] in Hin. destruct Hin as [<-|[]].
  cbn [R_Z0 YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hr. rewrite U2 in Hr. lia.
- intros a Pa. exact (apresent_grows (w_H W) mem _ a HG Pa).
Qed.

End g.
