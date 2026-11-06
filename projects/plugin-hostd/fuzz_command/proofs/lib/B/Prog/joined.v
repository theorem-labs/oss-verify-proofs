(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: the program walk of joined on the ASan build of plugin-hostd/fuzz_command, in the
   shape of cgif_file_fuzzer's walks (lib/A/ACb8.v, lib/A/ACh2.v): the symbolic executor over the position-abstract
   listing (CmdPaLib.v, PaLibF.v, PaCallRun.v) with the shadow tokens of PaShadow.v, the malloc call through
   amalloc04_sub and the memcpy calls through aj_intrin_atS (PaCall.v), and the strlen calls through PaArt.v's
   aj_art_at (jw_art_at below also keeps the entry's promise that a present byte stays present). *)
(* Modified by Theorem Labs, 2026-10: re-walked from lib/A/Prog/joined.v (a working branch) for
   fuzz_command.asan-ubsan (entry 0x88b50, 215 instructions, frame 128 bytes). The six codegen differences this walk
   follows: len is spilled to 16(sp) (part of jframe here, not a register), loop A counts max(n,0) down in s7 and
   recomputes the shadow address of w->w + 8i each pass, loop B keeps ~res in s10 and the shadow index of &w->w in
   s11 (the separator ' ' is in s0), the terminator's address is formed on both paths into 0x88dac, the malloc call
   and its abort edge are unchanged, and the error stub of *len needs no `mv a0`.
   The 17 UBSan traps (all branching to the `unimp` at 0x88e24) are decided by the seeds' facts and two seeded
   unsigned conditions; none of them is a goal of this walk. The frame chain the malloc call reads (chain_pre) is
   afn_pre's own chain when n = 0 (s0 is still the caller's) and the empty chain below alloc_ceiling when n > 0
   (s0 is the running length): a Theorem Labs lane's PASS4-REFIT.md section B, achain_chain_pre. The statement has no premise on
   the stack above len (pass 5b). *)
(* The walk: the entry and the prologue (jw_entry); loop A, one word per pass, sums |w_k| + 1 with the strlen entry
   (jw_loopA, by induction on the words left); the malloc call of join_need ws + 1 bytes (jw_call); the null check and
   the block's first byte (jw_M2); loop B, one word per pass, writes the separator and the word with __asan_memcpy
   (jw_loopB, jw_C, by induction on the words left; the cursor stays below join_need ws + 1, jw_cur_S); the
   terminator, *len, the epilogue and ret (jw_final). Each loop head and each point after a call starts a fresh
   symbolic state from the concrete facts its state carries (LA, LB, the premises of jw_C, jw_M2 and jw_final).
   tjoined_core proves tjoined_spec (lib/B/Prog/joined_c.v) with the premises in another order. The proof rests on the
   statement's own hypotheses (AMALLOC4, AMEMCPY, ASTRLEN), TL (CmdPaLib.v PALib) and the per-binary record HB, IMG
   (the allocator record of the image's symbols and the image facts), from which CmdRecFacts.v gives the read-only
   bytes the journal keeps as image bytes (cmd_ro_prog_apart) and the readable word after a word's terminator
   (cmd_heap_tail_vis, the strlen entry's atail_vis; every word is a live block). The struct's fields and *len lie in
   the stack window, whose shadow AR's zshadow_ok keeps usable (jw_stack_ra). A Theorem Labs lane's read-only words at each strlen
   call (rt_rom_view) come from the statement's arodata_okP. *)
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP00 YP0i YCbn.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import PaTable PaSym.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YN3v YI04 YG0s.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import PaStep.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YI16 YG0p YC5d YG0q.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require YI08.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import PaRun PaShadow PaJournal CmdSyms CmdList CmdPa CmdPaLib.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import PaDenot PaSB PaLibG PaLibH PaLibF PaCallRun PaCall.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Rt Require Import RtDefs RtString.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require Import RecFacts RecInv.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require joined_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import CmdGlob CmdBase CmdRep CmdObj PaArt joined_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B Require Import YF0m.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import CmdRecFacts.
Import ListNotations.
Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.
Module PJoin := OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog.joined_c.
(* the words joined so far: the plain model's join_sp and join_need over a prefix of the word list *)
Lemma jw_join_sp_snoc : forall l w, join_sp (l ++ [w]) = match l with [] => w | _ :: _ => join_sp l ++ SPACE :: w end.
Proof.
induction l as [|a l IH]; intros w; [reflexivity|].
cbn [app]. destruct l as [|b l']; [reflexivity|].
change (join_sp (a :: (b :: l') ++ [w])) with (a ++ SPACE :: join_sp ((b :: l') ++ [w])).
rewrite IH. change (join_sp (a :: b :: l')) with (a ++ SPACE :: join_sp (b :: l')).
rewrite <- app_assoc. reflexivity.
Qed.
Lemma jw_firstn_S : forall {A} (l : list A) i d, (i < length l)%nat -> firstn (S i) l = firstn i l ++ [nth i l d].
Proof.
intros A l. induction l as [|a l IH]; intros i d Hi; cbn in Hi; [lia|].
destruct i as [|i]; [reflexivity|]. cbn [firstn nth]. rewrite (IH i d) by lia. reflexivity.
Qed.
Lemma jw_need_app : forall l1 l2, PJoin.join_need (l1 ++ l2) = PJoin.join_need l1 + PJoin.join_need l2.
Proof. induction l1 as [|a l1 IH]; intros l2; cbn [app]; unfold PJoin.join_need in *; cbn [fold_right]; [lia|]. rewrite IH. lia. Qed.
Lemma jw_need_nonneg : forall l, 0 <= PJoin.join_need l.
Proof. induction l as [|a l IH]; unfold PJoin.join_need in *; cbn [fold_right]; lia. Qed.
Lemma jw_need_firstn : forall l i, PJoin.join_need (firstn i l) <= PJoin.join_need l.
Proof.
intros l i. rewrite <- (firstn_skipn i l) at 2. rewrite jw_need_app. pose proof (jw_need_nonneg (skipn i l)). lia.
Qed.
Lemma jw_need_nth : forall l k, (k < length l)%nat -> Z.of_nat (length (nth k l [])) + 1 <= PJoin.join_need l.
Proof.
induction l as [|w l IH]; intros k Hk; [cbn in Hk; lia|].
pose proof (jw_need_nonneg l) as H0.
destruct k as [|k]; cbn [nth]; unfold PJoin.join_need in *; cbn [fold_right].
- lia.
- cbn [length] in Hk. specialize (IH k ltac:(lia)). lia.
Qed.
Lemma jw_need_S : forall ws i, (i < length ws)%nat ->
PJoin.join_need (firstn (S i) ws) = PJoin.join_need (firstn i ws) + Z.of_nat (length (nth i ws [])) + 1.
Proof.
intros ws i Hi. rewrite (jw_firstn_S ws i []) by exact Hi. rewrite jw_need_app. unfold PJoin.join_need at 2. cbn [fold_right]. lia.
Qed.
Lemma jw_sp_S : forall ws i, (i < length ws)%nat ->
join_sp (firstn (S i) ws) = join_sp (firstn i ws) ++ (if (i =? 0)%nat then [] else [SPACE]) ++ nth i ws [].
Proof.
intros ws i Hi. rewrite (jw_firstn_S ws i []) by exact Hi. rewrite jw_join_sp_snoc.
destruct i as [|i]; [reflexivity|].
destruct ws as [|a ws]; [cbn in Hi; lia|]. cbn [firstn Nat.eqb]. reflexivity.
Qed.
Lemma jw_len_sp : forall l, l <> [] -> Z.of_nat (length (join_sp l)) = PJoin.join_need l - 1.
Proof.
induction l as [|a l IH]; intros Hl; [exfalso; exact (Hl eq_refl)|].
destruct l as [|b l'].
- cbn [join_sp]. unfold PJoin.join_need. cbn [fold_right]. lia.
- specialize (IH ltac:(discriminate)).
  change (join_sp (a :: b :: l')) with (a ++ SPACE :: join_sp (b :: l')).
  rewrite length_app. cbn [length]. rewrite Nat2Z.inj_add, Nat2Z.inj_succ, IH.
  change (PJoin.join_need (a :: b :: l')) with (Z.of_nat (length a) + 1 + PJoin.join_need (b :: l')). lia.
Qed.
Lemma jw_len_sp_le : forall l, Z.of_nat (length (join_sp l)) <= PJoin.join_need l.
Proof.
intros [|a l]; [cbn; lia|]. rewrite jw_len_sp by discriminate. lia.
Qed.
(* the symbolic states the walk starts from: at the entry, the head of loop A (0x88bf0), after the malloc call
   (0x88c4c), the head of loop B (0x88c9c), after the memcpy call (0x88d60) and the terminator (0x88dac).
   Atom 32 is the shadow base in each. The seeds carry the facts that decide the 17 UBSan traps: the 8-alignment of
   w (atom 10), of w->w (atom 33) and of w->w + 8i (atom 35), the heap ranges of w->w, w->w + 8i and the fresh
   block, the cursor's bound (atom 23), ~res (atom 26, jNOT) and the two seeded unsigned conditions
   w->w + 8i >=u w->w. *)
Definition jSB : Z := SHADOW_OFF.
Definition jBx : sv := SOff 32 0.
Definition jBspan : Z * Z := (SHADOW_OFF, SHADOW_OFF + 2 ^ 44 - 1).
Definition jstklo : Z := 0x7fff7f800000 - 16.
Definition jstkhi : Z := 2 ^ 47 - 32.
Definition jheaphi : Z := 2 ^ 47 - 16.
Definition jstkhi8 : Z := 2 ^ 47 - 8.
Definition jshx (n : nat) : sv := SAlu ALU_ADD (SAlu ALU_SRL (SOff n 0) (SLit 3)) (SOff 32 0).
Definition jsrl (n : nat) (c : Z) : sv := SAlu ALU_SRL (SOff n c) (SLit 3).
(* ~p of a pointer p <= CEIL_MAX (alloc_ceiling's upper bound, Reusable/YM05.v) *)
Definition jNOT : afact := mkAF (2 ^ 64 - 1 - 140737479966720) (2 ^ 64 - 1) 0.
Definition PC_A : Z := 9920.
Definition PC_M2 : Z := 10012.
Definition PC_B : Z := 10092.
Definition PC_C : Z := 10288.
Definition PC_F : Z := 10364.
Definition j_struct : YP09.region :=
YP09.mkRegion (Some 10%nat) 16 28 0 0 [YP09.mkChunk 16 (CVal 8 (SOff 33 0)); YP09.mkChunk 24 (CVal 4 (SOff 34 0))].
Definition ssE : sstate := mkSS AF_joined sr_atoms [stack_region 128; got_regionP; bcell_regionP 32; j_struct] None
(mkFacts [(2%nat, mkAF (2^46) (2^47) 4); (10%nat, mkAF jstklo jstkhi 3); (32%nat, mkAF jSB jSB 0);
  (33%nat, mkAF 4096 jheaphi 3); (34%nat, mkAF 0 (2^31 - 1) 0)] [] []).
Definition regsA : list sv := Eval vm_compute in
sr_set (sr_set (sr_set (sr_set (sr_set sr_atoms 21 (SOff 32 0)) 22 (jshx 9)) 24 (SLit 1)) 25 (SOff 19 0)) 27 (jsrl 18 0).
Definition ssA : sstate := mkSS PC_A regsA [YP09.mkRegion (Some 19%nat) 0 8 0 0 [YP09.mkChunk 0 (CVal 8 (SOff 33 0))]] None
(mkFacts [(19%nat, mkAF 4096 jheaphi 3); (20%nat, mkAF 4096 jheaphi 0); (32%nat, mkAF jSB jSB 0)]
 [mkAC BC_GEU (SOff 19 0) (SOff 20 0)] []).
Definition regsB : list sv := Eval vm_compute in
sr_set (sr_set (sr_set (sr_set sr_atoms 27 (jshx 18)) 22 (jshx 9)) 21 (SOff 32 0)) 8 (SLit 32).
Definition ssB : sstate := mkSS PC_B regsB
[YP09.mkRegion (Some 18%nat) 0 8 0 0 [YP09.mkChunk 0 (CVal 8 (SOff 33 0))];
 YP09.mkRegion (Some 9%nat) 0 4 0 0 [YP09.mkChunk 0 (CVal 4 (SOff 34 0))];
 YP09.mkRegion (Some 35%nat) 0 8 0 0 [YP09.mkChunk 0 (CVal 8 (SOff 36 0))];
 YP09.mkRegion (Some 37%nat) 0 1 0 1 []] None
(mkFacts [(9%nat, mkAF jstklo jstkhi8 0); (18%nat, mkAF jstklo jstkhi8 0); (19%nat, mkAF 4096 jheaphi 0);
  (23%nat, mkAF 0 MALLOC_MAX 0); (26%nat, jNOT); (32%nat, mkAF jSB jSB 0); (33%nat, mkAF 4096 jheaphi 0);
  (34%nat, mkAF 1 (2^31 - 1) 0); (35%nat, mkAF 4096 jheaphi 3); (37%nat, mkAF 4096 jheaphi 0)]
 [mkAC BC_GEU (SOff 35 0) (SOff 33 0)]
 [(SAlu ALU_ADD (SOff 33 0) (SOff 24 0), SOff 35 0); (SAlu ALU_ADD (SOff 24 0) (SOff 33 0), SOff 35 0);
  (SAlu ALU_ADD (SOff 19 0) (SOff 23 0), SOff 37 0)]).
Definition SHB : list shent := [mkSHE 37 0 1].
Definition j_saved : list Z := [1; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27].
Definition j_frame_region : YP09.region := YP09.mkRegion (Some 2%nat) 16 128 0 0
(YP09.mkChunk 16 (CVal 8 (SOff 47 0))
 :: map (fun j => YP09.mkChunk (120 - 8 * Z.of_nat j) (CVal 8 (SOff (33 + j) 0))) (seq 0 13)).
Definition regsF : list sv := Eval vm_compute in sr_set (sr_set sr_atoms 21 (SOff 32 0)) 10 (SOff 46 0).
Definition ssF : sstate := mkSS PC_F regsF
[j_frame_region; YP09.mkRegion (Some 46%nat) 0 1 0 1 []; YP09.mkRegion (Some 47%nat) 0 8 0 8 []] None
(mkFacts [(2%nat, mkAF (2^46) (2^47) 4); (32%nat, mkAF jSB jSB 0); (46%nat, mkAF 4096 jheaphi 0);
  (47%nat, mkAF jstklo jstkhi8 3)] [] []).
Definition SHF : list shent := [mkSHE 46 0 1].
Definition regsC : list sv := Eval vm_compute in
sr_set (sr_set (sr_set sr_atoms 21 (SOff 32 0)) 22 (jshx 9)) 27 (jshx 18).
Definition ssC : sstate := mkSS PC_C regsC [YP09.mkRegion (Some 9%nat) 0 4 0 0 [YP09.mkChunk 0 (CVal 4 (SOff 33 0))]] None
(mkFacts [(9%nat, mkAF jstklo jstkhi8 0); (20%nat, mkAF 0 (2^28) 0); (23%nat, mkAF 0 MALLOC_MAX 0); (26%nat, jNOT);
  (32%nat, mkAF jSB jSB 0); (33%nat, mkAF 1 (2^31 - 1) 0)] [] []).
(* after the malloc call (0x88c4c): a0 the fresh block, the slot at 8(sp), the struct's n *)
Definition regsM2 : list sv := Eval vm_compute in
sr_set (sr_set (sr_set sr_atoms 21 (SOff 32 0)) 22 (jshx 9)) 27 (jsrl 18 0).
Definition ssM2 : sstate := mkSS PC_M2 regsM2
[YP09.mkRegion (Some 10%nat) 0 1 0 1 []; YP09.mkRegion (Some 2%nat) 8 16 8 16 [];
 YP09.mkRegion (Some 9%nat) 0 4 0 0 [YP09.mkChunk 0 (CVal 4 (SOff 33 0))]] None
(mkFacts [(2%nat, mkAF (2^46) (2^47) 4); (9%nat, mkAF jstklo jstkhi8 0); (10%nat, mkAF 4096 jheaphi 0); (32%nat, mkAF jSB jSB 0);
  (33%nat, mkAF 0 (2^31 - 1) 0)] [] []).
Definition SHM2 : list shent := [mkSHE 10 0 1].
Section b. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section d.
Context {PI : PAImg cmd_listing}.
#[local] Notation SEGS := (@pa_segs _ cmd_listing PI).
#[local] Notation VAL := (@pa_val _ cmd_listing PI).
#[local] Notation SIG s := (@pa_sigma _ cmd_listing PI s).
#[local] Notation BASE := (@pa_val _ cmd_listing PI A_TEXT).
#[local] Notation rdW W mem := (aview SEGS (w_H W) mem).
Section e.
Variable B : asyms.
Let LAWS : AR_laws SEGS B := AR_laws_ok SEGS B.
Variable MT : ameter_ops.
#[local] Notation RLO := CMD_RLO.
#[local] Notation RHI := CMD_RHI.
(* the runtime entries the call reaches: the statement's own hypotheses *)
Hypothesis AMALLOC4 : forall fx0 : YK11.FPState, @amalloc04_rule fx0 rc SK SEGS B MT.
Hypothesis AMEMCPY : forall fx0 : YK11.FPState, @aintrin_realizes fx0 rc SEGS B OCpy (SIG CS___asan_memcpy).
Hypothesis ASTRLEN : forall fx0 : YK11.FPState, @astrlen_realizes fx0 rc SEGS B (SIG CS___interceptor_trampoline_strlen).
(* the per-binary record (a Theorem Labs lane's ruling, a Theorem Labs lane's RULING-STMT.md; CmdRecFacts.v): the malloc trampoline
   is the malloc rule's entry and the shadow base cell is the record's (TL); the allocator record of the image's
   symbols (HB) and the image facts (IMG), from which: the bytes after a word's terminator up to its 8-byte word are
   readable (cmd_heap_tail_vis, every word being in a live block); every read-only byte is in the image
   (cmd_ro_prog_apart) *)
Hypothesis TL : PALib B.
Hypothesis HB : CmdBSyms B.
Hypothesis IMG : cmd_img_facts SEGS B.
Let cmd_heap_tail_vis : forall ly S (W : world SEGS) mem md p n e, AR SEGS B ly S W mem md ->
In (p, n) (ablocks B ly S) -> p <= e < p + req_size n -> atail_vis SEGS W mem e := cmd_heap_tail_vis SEGS B LAWS HB.
Let cif_ro_img : forall a, in_roP SEGS RLO RHI a -> in_img SEGS a :=
  fun a H => proj1 (cmd_ro_prog_apart SEGS B LAWS HB IMG a H).
Let errno_low := pal_env B TL.
Let RUN := paj_run B LAWS. Let RUNTO := paj_run_to B LAWS.
Let BR := paj_branch (PI := PI). Let RET := paj_ret_at (PL := PL_cmd) (PI := PI).
(* a stack range at zero shadow: AR keeps [ly_stk_lo, ly_stk_hi) so (zero_shadow_ranges, YG0n.v:188) *)
Lemma jw_stack_ra : forall ly S (W : world SEGS) mem md a n,
AR SEGS B ly S W mem md -> ly_stk_lo ly <= a -> a + n <= ly_stk_hi ly ->
range_addressable (rdW W mem) SHADOW_OFF a n.
Proof.
intros ly S W mem md a n HAR Hlo Hhi.
pose proof (am_layout _ _ _ _ (proj1 HAR)) as LO. destruct (lo_top _ LO) as (_ & _ & _ & _ & Hpl & Hph & _).
unfold page_aligned in Hpl, Hph. try unfold PGSZ in Hpl, Hph.
assert (A8 : forall x, x mod 4096 = 0 -> x mod 8 = 0).
{ intros x Hx. apply Z.mod_divide; [lia|]. apply Z.mod_divide in Hx; [|lia].
  apply (Z.divide_trans 8 4096); [exists 512; reflexivity | exact Hx]. }
apply (range_addressable_sub _ _ (ly_stk_lo ly) (ly_stk_hi ly - ly_stk_lo ly)); [|lia|lia].
apply zero_shadow_range; [exact (A8 _ Hpl) | rewrite Zminus_mod, (A8 _ Hpl), (A8 _ Hph); reflexivity |].
exact (al_zshadow _ _ LAWS ly S W mem md _ HAR ltac:(left; reflexivity)).
Qed.
(* PaArt's aj_art_at, keeping also the entry's promise that every present byte stays present (art_post, RtDefs.v) *)
Lemma jw_art_at : forall stk (Eb : Z -> Prop) pc W regsT memT STK sp0 FP ly S W0 mem md own lyc Sc mdc k (o : Z) raw
(Qr : bvmap 5 word -> (word -> option byte) -> Prop),
ajournal SEGS B STK sp0 FP ly S W0 mem md own lyc Sc W memT mdc k ->
spZ regsT = sp0 + o -> o mod 16 = 0 -> o <= 0 -> 0 <= stk -> stk - o <= STK ->
getr regsT 1 = raw ->
(forall a, Eb a -> as_errno B <= a < as_errno B + 4) ->
SRr SEGS W (cfg_at SEGS pc regsT memT mdc) (art_post SEGS B stk lyc Sc W regsT memT mdc Eb Qr) ->
SRr SEGS W (mkCfg (mkst regsT (Z_to_bv 64 pc) memT (seg_rom SEGS)) mdc)
(fun W2 c2 => W2 = W /\ exists regs2 mem2 md2,
c2 = mkCfg (mkst regs2 raw mem2 (seg_rom SEGS)) md2 /\
ajournal SEGS B STK sp0 FP ly S W0 mem md own lyc Sc W mem2 md2 k /\
aregs_preserved regsT regs2 /\ Qr regs2 mem2 /\
(forall a, 0 <= a < 2 ^ 64 -> ~ (sp0 + o - stk <= a < sp0 + o) -> ~ Eb a ->
aview SEGS (w_H W) mem2 a = aview SEGS (w_H W) memT a) /\
(forall a, apresent (w_H W) memT a -> apresent (w_H W) mem2 a)).
Proof.
intros stk Eb pc W regsT memT STK sp0 FP ly S W0 mem md own lyc Sc mdc k o raw Qr
HJ Hsp Hal Hneg Hstk Hbud Hraw HEb HC.
pose proof HJ as (HAR & Hly & Hsecs & Hwle & Hio & Hfrs & Hnev & Hk & _ & _ & _ & _ & _ & Hpres & Hstatic & F5 & HQT).
pose proof Hstatic as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop2 & Htop).
pose proof Hly as (_ & _ & _ & _ & _ & _ & _ & _ & Etop & Eslo & Eshi & _).
eapply SRr_mono; [exact HC|].
cbv beta. intros W2 c2 _ (-> & regs2 & mem2 & md2 & -> & HAR2 & HP & Hsame & HQ & Hfr & Hpres2 & Hscr).
split; [reflexivity|]. exists regs2, mem2, md2.
split; [unfold cfg_at, raZ, w64; rewrite Hraw, Z_to_bv_bv_unsigned; reflexivity|].
split.
{ assert (HJ1 : ajournal SEGS B stk (spZ regsT) [] lyc Sc W memT mdc [] lyc Sc W mem2 md2 0).
{ eapply (call_effect_journal SEGS B LAWS pa_segs_low errno_low stk lyc Sc W regsT memT mdc lyc Sc W mem2 md2
(fun _ => False) [] [] 0);
[exact HAR2 | apply layout_le_refl | apply wle_refl | apply same_io_materialized; exact Hsame | | exact Hscr | exact HAR
| | reflexivity | lia | lia | lia | intros a [] | intros p n i H1 H2; exfalso; exact (H2 H1) | exact HQT].
- intros a H0 _ _ H3 _. apply (Hfr a H0).
+ intros Hs. apply H3. left. exact Hs.
+ intros He. apply H3. right. exact (HEb a He).
- unfold astk_ok, ly_bot in *. rewrite Etop, Eslo, Eshi. rewrite Hsp.
repeat split; first [rewrite Z.add_mod, Hal16, Hal by lia; reflexivity | lia]. }
pose proof (ajournal_sub_tok SEGS B LAWS pa_segs_low STK sp0 FP ly S W0 mem md own lyc Sc W memT mdc k stk (spZ regsT) []
[] lyc Sc W mem2 md2 0 HJ HJ1 ltac:(lia) ltac:(lia) ltac:(intros a Ha; exfalso; exact (inFP_nil a Ha))) as HJ2.
rewrite app_nil_l, Z.add_0_r in HJ2. exact HJ2. }
split; [exact HP|]. split; [exact HQ|]. split; [|exact Hpres2].
intros a Ha Hw He. apply (Hfr a Ha); [|exact He]. unfold ascratch_stk. rewrite Hsp. exact Hw.
Qed.
(* the entry context: the statement's quantified values and premises *)
Section ctx.
Variables (ly : alayout) (S : astate) (W : world SEGS) (regs : bvmap 5 word) (mem : word -> option byte) (md : Model)
  (ch : list (Z * Z * Z)) (W0 arr outp : Z) (wp : list Z) (ws : list (list byte)).
Hypothesis HPRE : afn_pre SEGS B JOINED_STK ly S W regs mem md ch.
Hypothesis HROD : arodata_okP SEGS RLO RHI B (rdW W mem).
Hypothesis H10 : getr regs 10 = w64 W0.
Hypothesis H11 : getr regs 11 = w64 outp.
Hypothesis HW1 : spZ regs <= W0 + 16.
Hypothesis HW2 : W0 + 32 <= ly_stk_hi ly.
Hypothesis HWR : range_addressable (rdW W mem) SHADOW_OFF (W0 + 16) 12.
Hypothesis HLEN : length wp = length ws.
Hypothesis HN31 : Z.of_nat (length ws) < 2 ^ 31.
Hypothesis HVN : aval_mem (rdW W mem) (W0 + 24) 4 (Z.of_nat (length ws)).
Hypothesis HVA : aval_mem (rdW W mem) (W0 + 16) 8 arr.
Hypothesis HAB : in_blockA (ablocks B ly S) arr (8 * Z.of_nat (length ws)).
Hypothesis HWS : forall k, (k < length ws)%nat ->
  aval_mem (rdW W mem) (arr + 8 * Z.of_nat k) 8 (nth k wp 0) /\ 0 <= nth k wp 0 < 2 ^ 64 /\
  in_blockA (ablocks B ly S) (nth k wp 0) (Z.of_nat (length (nth k ws [])) + 1) /\
  astr_atR (rdW W mem) (nth k wp 0) (nth k ws []).
Hypothesis HNEED : PJoin.join_need ws + 1 < MALLOC_MAX.
Hypothesis HO1 : spZ regs <= outp.
Hypothesis HO2 : outp + 8 <= ly_stk_hi ly.
Hypothesis HO3 : outp mod 8 = 0.
Hypothesis HOS : outp + 8 <= W0 + 16 \/ W0 + 32 <= outp.
Hypothesis HEV : st_nev S + EV_JOINED <= EV_MAX.
Hypothesis HLIVE : blocks_bytes S + LIVE_JOINED <= LIVE_MAX.
Hypothesis MOK : mo_ok MT S (XM_JOINED MT ws).
(* what tjoined_core derives from the statement (HWR and HO2: the struct's fields and *len lie in the stack window,
   jw_stack_ra), the statement's premises on *len (HOTOP and its 8 bytes present, HOPR) and the two alignment
   premises the UBSan traps need (HW8 at 0x88b90, HARR8 at 0x88c08 / 0x88cc8 / 0x88d3c). No premise on the stack
   above len is needed: this build's malloc call reads s0, the running length *)
Hypothesis HOTOP : outp + 8 <= ly_top ly.
Hypothesis HOPR : forall i, 0 <= i < 8 -> apresent (w_H W) mem (outp + i).
Hypothesis HW8 : W0 mod 8 = 0.
Hypothesis HARR8 : arr mod 8 = 0.
#[local] Notation sp0 := (spZ regs).
#[local] Notation nW := (Z.of_nat (length ws)).
Definition FPj : list (Z * Z) := [(outp, outp + 8)].
Definition jtot : Z := PJoin.join_need ws + 1.
(* the frame: ra and s0..s11 of the entry, saved at sp0 - 8 .. sp0 - 104, and len spilled at sp0 - 112 *)
Definition jframe (m : word -> option byte) : Prop :=
(forall j r, nth_error j_saved j = Some r -> val_mem SEGS m (sp0 - 8 - 8 * Z.of_nat j) 8 (bv_unsigned (getr regs (Z_to_bv 5 r))))
/\ val_mem SEGS m (sp0 - 112) 8 outp.
Definition JQ : alayout -> astate -> world SEGS -> bvmap 5 word -> (word -> option byte) -> Model -> Prop :=
fun ly' S' W' regs' mem' md' => exists res : Z,
 getr regs' 10 = w64 res /\ 4096 <= res < 2 ^ 64 /\
 Permutation (ablocks B ly' S') ((res, PJoin.join_need ws + 1) :: ablocks B ly S) /\
 Forall (fun qk => iv_apart res (PJoin.join_need ws + 1) (fst qk) (snd qk)) (ablocks B ly S) /\
 in_blockA (ablocks B ly' S') res (PJoin.join_need ws + 1) /\
 abytes_atR (rdW W' mem') res (join_sp ws ++ [Z_to_bv 8 0]) /\
 aval_mem (rdW W' mem') outp 8 (Z.of_nat (length (join_sp ws))) /\
 (forall p n i, In (p, n) (ablocks B ly S) -> 0 <= i < n -> rdW W' mem' (p + i) = rdW W mem (p + i)) /\
 blocks_bytes S' <= blocks_bytes S + LIVE_JOINED /\
 mo_le MT S S' (XM_JOINED MT ws).
Definition JPOST : world SEGS -> config -> Prop := apost_base SEGS B JOINED_STK FPj regs ly S W mem md EV_JOINED JQ.
Ltac jctx :=
pose proof HPRE as (HAR0 & Hra0 & Hra40 & Hgp0 & Htp0 & Hstk0 & Hpres0 & Hch0 & HQT0);
pose proof Hstk0 as (Hal160 & HSTK0 & Hceil0 & Hslo0 & Hshi0 & H470 & Hbot0 & Htop0 & Htop20);
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5);
assert (HJS : JOINED_STK = 16512) by reflexivity;
assert (Hes : ESTACK = 4096) by reflexivity; assert (Has : ASTACK = 16384) by reflexivity.
Lemma jw_nfp : forall a, a < spZ regs -> ~ inFP FPj a.
Proof. intros a Ha (r & [<- | []] & Hr). cbn [fst snd] in Hr. lia. Qed.
Lemma jw_open : ~ YI16.sink_open_fp FPj.
Proof. intros (r & [<- | []] & Hr). cbn [fst snd] in Hr. jctx. lia. Qed.
(* the layout and stack window at a later state of the walk *)
Lemma jw_ly : forall lyc Sc Wc mc mdc kk,
ajournal SEGS B JOINED_STK sp0 FPj ly S W mem md [] lyc Sc Wc mc mdc kk ->
ly_stk_lo lyc = ly_stk_lo ly /\ ly_stk_hi lyc = ly_stk_hi ly /\ ly_top lyc = ly_top ly.
Proof.
intros lyc Sc Wc mc mdc kk HJ. pose proof HJ as (_ & Hly & _).
pose proof Hly as (_ & _ & _ & _ & _ & _ & _ & _ & Etop & Eslo & Eshi & _). auto.
Qed.
(* the struct's two fields, unchanged at any later state of the walk, and addressable *)
Lemma jw_struct : forall lyc Sc Wc mc mdc kk,
ajournal SEGS B JOINED_STK sp0 FPj ly S W mem md [] lyc Sc Wc mc mdc kk ->
aval_mem (rdW Wc mc) (W0 + 24) 4 nW /\ aval_mem (rdW Wc mc) (W0 + 16) 8 arr /\
range_addressable (rdW Wc mc) SHADOW_OFF (W0 + 16) 16.
Proof.
intros lyc Sc Wc mc mdc kk HJ. jctx.
pose proof HJ as (HAR' & _ & _ & _ & _ & _ & _ & _ & F1 & _).
destruct (jw_ly _ _ _ _ _ _ HJ) as (Elo & Ehi & _).
assert (K : forall a, W0 + 16 <= a < W0 + 32 -> rdW Wc mc a = rdW W mem a).
{ intros a Ha. apply F1; [lia | lia |]. intros (r & [<- | []] & Hr). cbn [fst snd] in Hr. lia. }
split; [intros k Hk; rewrite K by lia; exact (HVN k Hk)|].
split; [intros k Hk; rewrite K by lia; exact (HVA k Hk)|].
apply (jw_stack_ra lyc Sc Wc mc mdc); [exact HAR' | rewrite Elo; lia | rewrite Ehi; lia].
Qed.
(* the slot of the word array a loop reads, at any later state of the walk *)
Lemma jw_argv : forall k lyc Sc Wc mc mdc kk, (k < length ws)%nat ->
ajournal SEGS B JOINED_STK sp0 FPj ly S W mem md [] lyc Sc Wc mc mdc kk ->
4096 <= arr + 8 * Z.of_nat k /\ arr + 8 * Z.of_nat k + 8 <= alloc_ceiling /\
aval_mem (rdW Wc mc) (arr + 8 * Z.of_nat k) 8 (nth k wp 0) /\
range_addressable (rdW Wc mc) SHADOW_OFF (arr + 8 * Z.of_nat k) 8.
Proof.
intros k lyc Sc Wc mc mdc kk Hk HJ. jctx.
pose proof HJ as (HAR' & _ & _ & _ & _ & _ & _ & _ & F1 & F2 & F3 & F4 & Hgone & _).
destruct HAB as (b & m & Hin & Hb1 & Hb2).
destruct (al_blocks _ _ LAWS _ _ _ _ _ b m HAR0 Hin) as (_ & Hb4096 & Hbceil & _ & _ & _ & Hm).
pose proof (req_size_pos m (proj1 Hm)) as [Hq1 Hq2].
assert (Hin' : In (b, m) (ablocks B lyc Sc)).
{ destruct (in_dec (fun x y : Z * Z => ltac:(decide equality; apply Z.eq_dec)) (b, m) (ablocks B lyc Sc)) as [H|H]; [exact H|].
  exfalso. apply (jw_nfp (b + 0) ltac:(lia)). exact (Hgone b m 0 Hin H ltac:(lia)). }
split; [lia|]. split; [lia|]. split.
- intros j Hj. replace (arr + 8 * Z.of_nat k + Z.of_nat j) with (b + (arr + 8 * Z.of_nat k + Z.of_nat j - b)) by lia.
  rewrite (F2 b m _ Hin Hin'); [| lia | apply jw_nfp; lia].
  replace (b + (arr + 8 * Z.of_nat k + Z.of_nat j - b)) with (arr + 8 * Z.of_nat k + Z.of_nat j) by lia.
  exact (proj1 (HWS k Hk) j Hj).
- apply (range_addressable_of_block SEGS B LAWS lyc Sc Wc mc mdc b m); [exact HAR' | exact Hin' | lia | lia].
Qed.
(* a word, at any later state of the walk: its bytes kept, readable as the strlen entry asks, its tail word readable,
   and where it lies (a block that was live at the entry) *)
Lemma jw_word : forall k lyc Sc Wc mc mdc kk, (k < length ws)%nat ->
ajournal SEGS B JOINED_STK sp0 FPj ly S W mem md [] lyc Sc Wc mc mdc kk ->
4096 <= nth k wp 0 /\ nth k wp 0 + Z.of_nat (length (nth k ws [])) + 1 <= alloc_ceiling /\
Z.of_nat (length (nth k ws [])) < 2 ^ 28 /\
astr_atR (rdW Wc mc) (nth k wp 0) (nth k ws []) /\
(forall regsT stk, alloc_ceiling <= spZ regsT - stk ->
  aread_ok SEGS stk Wc regsT mc (nth k wp 0) (Z.of_nat (length (nth k ws [])) + 1)) /\
atail_vis SEGS Wc mc (nth k wp 0 + Z.of_nat (length (nth k ws []))) /\
((exists b m, In (b, m) (ablocks B ly S) /\ b <= nth k wp 0 /\ nth k wp 0 + Z.of_nat (length (nth k ws [])) + 1 <= b + m) \/
 (0x10000 <= nth k wp 0 /\ nth k wp 0 + Z.of_nat (length (nth k ws [])) + 1 <= 0x606000)).
Proof.
intros k lyc Sc Wc mc mdc kk Hk HJ. jctx.
pose proof HJ as (HAR' & _ & _ & _ & _ & _ & _ & _ & F1 & F2 & F3 & F4 & Hgone & _).
pose proof (jw_need_nth ws k Hk) as Hnd. pose proof HNEED as HN28. unfold MALLOC_MAX in HN28.
destruct (HWS k Hk) as (_ & _ & HinB & Hstr).
set (p := nth k wp 0) in *. set (w := nth k ws []) in *. set (n := Z.of_nat (length w) + 1) in *.
destruct HinB as (b & m & Hin & Hb1 & Hb2).
destruct (al_blocks _ _ LAWS _ _ _ _ _ b m HAR0 Hin) as (_ & Hb4096 & Hbceil & _ & _ & _ & Hm).
pose proof (req_size_pos m (proj1 Hm)) as [Hq1 Hq2].
assert (Hin' : In (b, m) (ablocks B lyc Sc)).
{ destruct (in_dec (fun x y : Z * Z => ltac:(decide equality; apply Z.eq_dec)) (b, m) (ablocks B lyc Sc)) as [H|H]; [exact H|].
  exfalso. apply (jw_nfp (b + 0) ltac:(lia)). exact (Hgone b m 0 Hin H ltac:(lia)). }
assert (KB : forall a, p <= a < p + n -> rdW Wc mc a = rdW W mem a).
{ intros a Ha. replace a with (b + (a - b)) by lia. apply (F2 b m _ Hin Hin'); [lia | apply jw_nfp; lia]. }
assert (Hstr' : astr_atR (rdW Wc mc) p w).
{ destruct Hstr as [Hb Hz]. split; [|exact Hz]. intros i Hi. rewrite KB; [apply Hb; exact Hi|].
  rewrite length_app in Hi. cbn [length] in Hi. lia. }
split; [lia|]. split; [lia|]. split; [lia|]. split; [exact Hstr'|]. split.
+ intros regsT stk Hs.
  split; [lia|]. split; [lia|]. split; [lia|]. split.
  { intros a Ha. split; [|unfold ascratch_stk; lia].
    destruct Hstr' as [Hb _]. replace a with (p + Z.of_nat (Z.to_nat (a - p))) by lia.
    rewrite Hb; [discriminate|]. rewrite length_app. cbn [length]. lia. }
  split; [apply (amem_range_of_block SEGS B LAWS lyc Sc Wc mc mdc b m); [exact HAR' | exact Hin' | lia | lia]|].
  split; [apply (range_addressable_of_block SEGS B LAWS lyc Sc Wc mc mdc b m); [exact HAR' | exact Hin' | lia | lia]|].
  intros _. apply (shadow_hull_vis_of_block SEGS B LAWS lyc Sc Wc mc mdc b m); [exact HAR' | exact Hin' | lia | lia | lia].
+ split; [apply (cmd_heap_tail_vis lyc Sc Wc mc mdc b m); [exact HAR' | exact Hin' | lia]|].
  left. exists b, m. split; [exact Hin | lia].
Qed.
(* the read-only bytes keep the image's values at any later state of the walk *)
Lemma jw_arod : forall lyc Sc Wc mc mdc kk,
ajournal SEGS B JOINED_STK sp0 FPj ly S W mem md [] lyc Sc Wc mc mdc kk -> arodata_okP SEGS RLO RHI B (rdW Wc mc).
Proof.
intros lyc Sc Wc mc mdc kk HJ a Hro Ho He. jctx.
pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & F3 & _).
pose proof (pa_img_range _ (cif_ro_img a Hro)) as Ha.
rewrite (F3 a (cif_ro_img a Hro) Ho He (fp_spares_closed FPj a jw_open (jw_nfp a ltac:(lia)))). exact (HROD a Hro Ho He).
Qed.
(* a Theorem Labs lane's read-only words at any later state of the walk: the in-segment half of arodata_okP (RtDefs.v rt_rom_view) *)
Lemma jw_rom : forall lyc Sc Wc mc mdc kk,
ajournal SEGS B JOINED_STK sp0 FPj ly S W mem md [] lyc Sc Wc mc mdc kk -> rt_rom_view SEGS B Wc mc.
Proof.
intros lyc Sc Wc mc mdc kk HJ a (sg & Hsg & Hw & Hr) Ho He.
exact (jw_arod lyc Sc Wc mc mdc kk HJ a (or_introl (ex_intro _ sg (conj Hsg (conj Hw Hr)))) Ho He).
Qed.
(* a value read through mrestrict is the value read through aview *)
Lemma jw_aval_of_val : forall H m a (n : nat) v, val_mem SEGS (mrestrict H m) a n v -> aval_mem (aview SEGS H m) a n v.
Proof.
intros H m a n v Hv k Hk. unfold aview. rewrite (Hv k Hk). cbn [option_map]. f_equal.
rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 8) with 256. apply Z.mod_small.
unfold YO0f.le_byte. apply Z.mod_pos_bound. lia.
Qed.
(* a register of a symbolic state whose value is not a plain atom (the shadow pointers and ~res) *)
Ltac jw_rawreg HS r Hr :=
  first [pose proof (st_ok_restrict_reg _ _ _ _ _ r HS) as Hr | pose proof (st_ok_pi_restrict_reg _ _ _ _ r HS) as Hr];
  cbn [ms_regs] in Hr;
  lazymatch type of Hr with _ = sv_denot ?Ex (sr_get ?a ?rr2) => let v := eval vm_compute in (sr_get a rr2) in change (sr_get a rr2) with v in Hr end.
(* the final segment, 0x88dac .. ret: the terminator at res + |join_sp ws| (a0 holds it on both paths into 0x88dac),
   the alignment check of len (0x88dc8, refuted by outp mod 8 = 0), the store of *len, the frame popped *)
Lemma jw_final : forall lyc Sc Wc rF mF dF res,
ajournal SEGS B JOINED_STK sp0 FPj ly S W mem md [] lyc Sc Wc mF dF 1 ->
ablocks B lyc Sc = ablocks B ly S ++ [(res, jtot)] -> 4096 <= res -> mo_le MT S Sc (XM_JOINED MT ws) ->
jframe (mrestrict (w_H Wc) mF) ->
(forall i, 0 <= i < 8 -> apresent (w_H Wc) mF (outp + i)) ->
abytes_atR (rdW Wc mF) res (join_sp ws) ->
getr rF 2 = w64 (sp0 - 128) -> getr rF 3 = w64 (as_gp B) -> getr rF 4 = w64 (as_tp B) ->
getr rF 10 = w64 (res + Z.of_nat (length (join_sp ws))) ->
getr rF 19 = w64 res -> getr rF 21 = w64 SHADOW_OFF -> getr rF 23 = w64 (Z.of_nat (length (join_sp ws))) ->
SRr SEGS Wc (mkCfg (mkst rF (Z_to_bv 64 (BASE + PC_F)) mF (seg_rom SEGS)) dF) JPOST.
Proof.
intros lyc Sc Wc rF mF dF res HJ Eab Hres MLE HFRa HOP HBY R2 R3 R4 R10 R19 R21 R23. jctx.
destruct HFRa as (HFR & HFRo).
set (c := Z.of_nat (length (join_sp ws))) in *.
assert (Hc : 0 <= c <= PJoin.join_need ws) by (pose proof (jw_len_sp_le ws); lia).
pose proof HJ as (HAR & Hly & _ & _ & _ & Hfrs & _).
destruct (jw_ly _ _ _ _ _ _ HJ) as (Elo & Ehi & Etop).
assert (Hres_in : In (res, jtot) (ablocks B lyc Sc)) by (rewrite Eab; apply in_or_app; right; left; reflexivity).
destruct (al_blocks _ _ LAWS _ _ _ _ _ res jtot HAR Hres_in) as (Hr16 & Hr4096 & Hrceil & Hrapp & Hrpres & _ & Hrm).
pose proof (req_size_pos jtot ltac:(unfold jtot; pose proof (jw_need_nonneg ws); lia)) as [Hq1 Hq2].
assert (Hcj : c < jtot) by (unfold jtot; lia).
pose proof alloc_ceiling_value as [_ HAC2].
(* the seed: atom 32 the shadow base, 33..45 the saved registers, 46 the terminator's address, 47 len *)
set (vsv := map (fun r => getr regs (Z_to_bv 5 r)) j_saved).
set (xF := Z_to_bv 64 jSB :: vsv ++ [Z_to_bv 64 (res + c); Z_to_bv 64 outp]).
set (E := Eimg (Ereg rF xF)).
assert (HEI : img_env VAL A_LIM E) by apply Eimg_env.
assert (EE : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E n = getr rF r)
  by (intros n r Hn; apply ew_Eimg_Ereg_nat; exact Hn).
assert (EX : forall j, (j < 100)%nat -> ew E (32 + j) = nth j xF (Z_to_bv 64 0)).
{ intros j Hj. unfold E. rewrite Eimg_low by (unfold A_TEXT; lia). apply ew_Ereg_extra. }
assert (EXn : forall n, (32 <= n < 132)%nat -> ew E n = nth (n - 32) xF (Z_to_bv 64 0)).
{ intros n Hn. replace n with (32 + (n - 32))%nat at 1 by lia. apply EX. lia. }
assert (E32 : ew E 32 = Z_to_bv 64 jSB) by exact (EX 0%nat ltac:(lia)).
assert (E46 : ew E 46 = Z_to_bv 64 (res + c)) by exact (EX 14%nat ltac:(lia)).
assert (E47 : ew E 47 = Z_to_bv 64 outp) by exact (EX 15%nat ltac:(lia)).
assert (Usp : bv_unsigned (ew E 2) = sp0 - 128) by (rewrite (EE 2%nat 2%bv eq_refl), R2; apply unsigned_lit_small; lia).
assert (U46 : bv_unsigned (ew E 46) = res + c) by (rewrite E46; apply unsigned_lit_small; lia).
assert (U47 : bv_unsigned (ew E 47) = outp) by (rewrite E47; apply unsigned_lit_small; lia).
assert (HS : st_ok_pi SEGS VAL E ssF (restrict (w_H Wc) (mkst rF (Z_to_bv 64 (BASE + PC_F)) mF (seg_rom SEGS)))).
{ rewrite restrict_mkst_fx. unfold ssF. apply pa_entry_st_ok_full.
  - change regsF with (sr_set (sr_set sr_atoms 21 (SOff 32 0)) 10 (SOff 46 0)).
    apply regs_ok_rereg; [apply regs_ok_rereg; [apply regs_ok_Eimg_Ereg | reflexivity |] | reflexivity |].
    + cbn [sv_denot]. rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned. exact R21.
    + cbn [sv_denot]. rewrite E46, Z.add_0_r, Z_to_bv_bv_unsigned. exact R10.
  - vm_compute. reflexivity.
  - repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
      cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val j_frame_region].
    + rewrite Usp. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
      lazymatch goal with |- Forall ?P ?l => let l2 := eval vm_compute in l in change (Forall P l2) end.
      repeat apply Forall_cons; try apply Forall_nil;
      lazymatch goal with |- YP09.chunk_ok _ _ _ _ (YP09.mkChunk ?off (CVal 8 (SOff ?n 0))) =>
        first
        [ let j := eval compute in (n - 33)%nat in let r := eval compute in (nth j j_saved 0) in
          apply (chunk_ok_val SEGS E _ (sp0 - 128) off 8 (SOff n 0) (bv_unsigned (getr regs (Z_to_bv 5 r))));
          [ let k := eval compute in (n - 32)%nat in let Ek := fresh in pose proof (EX k ltac:(lia)) as Ek; cbn [Nat.add] in Ek;
            cbn [sv_denot]; rewrite Ek; cbn [xF vsv nth map app j_saved];
            rewrite Z.add_0_r, !Z_to_bv_bv_unsigned; reflexivity
          | let HR := fresh in pose proof (bv_unsigned_in_range 64 (getr regs (Z_to_bv 5 r))) as HR;
            change (bv_modulus 64) with (2 ^ 64) in HR; cbn; lia
          | cbn; lia
          | replace (sp0 - 128 + off) with (sp0 - 8 - 8 * Z.of_nat j) by (cbn; lia); exact (HFR j r eq_refl) ]
        | apply (chunk_ok_val SEGS E _ (sp0 - 128) 16 8 (SOff 47 0) outp);
          [ cbn [sv_denot]; rewrite E47, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
          | change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); lia | cbn; lia
          | replace (sp0 - 128 + 16) with (sp0 - 112) by (cbn; lia); exact HFRo ] ] end.
    + rewrite U46. split; [lia|]. split; [lia|]. split; [|constructor].
      intros o Ho. apply (apresent_writable SEGS). apply (proj1 (Hrpres (res + c + o) ltac:(lia))).
    + rewrite U47. split; [lia|]. split; [lia|]. split; [|constructor].
      intros o Ho. apply (apresent_writable SEGS). apply HOP. lia.
  - apply pairwise_disjoint_of_extents. unfold extent_of_region.
    cbn [map YP09.r_base YP09.r_lo YP09.r_hi j_frame_region base_val]. rewrite Usp, U46, U47.
    cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd]. repeat split; lia.
  - split; [|split; exact I].
    cbn [f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
    rewrite Usp, U46, U47, E32. rewrite unsigned_lit_small by (unfold jSB, SHADOW_OFF; lia).
    unfold jstklo, jstkhi8, jheaphi, jSB. change (2 ^ 4) with 16. change (2 ^ 3) with 8. rewrite Z.pow_0_r, !Z.mod_1_r.
    repeat split; try exact I; try exact HO3; try lia.
    replace (sp0 - 128) with (sp0 + (-8) * 16) by lia. rewrite Z_mod_plus_full. exact Hal160. }
assert (UB : U E jBx = SHADOW_OFF) by (unfold jBx; apply U_atom; [rewrite E32; reflexivity | unfold SHADOW_OFF; lia]).
assert (SHOK : sh_ok SEGS jBx SHF E (mrestrict (w_H Wc) mF)).
{ unfold sh_ok, SHF. apply Forall_cons; [|apply Forall_nil].
  unfold shent_ok, app_apart. cbn [she_m she_lo she_hi].
  assert (U46' : U E (SOff 46 0) = res + c) by (apply U_atom; [exact E46 | lia]).
  rewrite UB, U46', <- (aview_rd_of SEGS). split.
  - apply (range_addressable_of_block SEGS B LAWS lyc Sc Wc mF dF res jtot); [exact HAR | exact Hres_in | lia | lia].
  - intros a Ha. destruct Hrapp as [_ [Hlow | [Hhi1 Hhi2]]]; unfold kLowShadowBeg, kHighMemBeg, SHADOW_OFF in *; lia. }
paj_run_tok RUN HS HJ SHOK jBspan.
{ rewrite <- (aview_rd_of SEGS).
  rewrite UB, (U_atom E 47 outp) by (first [exact E47 | lia]).
  apply (jw_stack_ra lyc Sc Wc mF dF); [exact HAR | rewrite Elo; lia | rewrite Ehi; lia]. }
{ unfold ssF. cbn [ss_mem].
  apply awr_ok_cons_ro; [cbn; lia|].
  eapply awr_ok_cons_gen; [reflexivity | exact U46 | |].
  { intros a Ha. cbn [YP09.r_wlo YP09.r_whi] in Ha. replace a with (res + c) by lia.
    eapply (awr_new_block_any SEGS B LAWS); [exact (ajournal_init SEGS B JOINED_STK FPj ly S W regs mem md ch HPRE) | exact HAR | exact Eab | | exact Hres_in | lia].
    unfold jtot; pose proof (jw_need_nonneg ws); lia. }
  eapply awr_ok_cons_gen; [reflexivity | exact U47 | |].
  { intros a Ha. cbn [YP09.r_wlo YP09.r_whi] in Ha. right; right; right; right. unfold awr_prog_or_caller. right; left.
    split; [exists (outp, outp + 8); split; [left; reflexivity | cbn; lia] | rewrite Etop; lia]. }
  apply awr_ok_nil. }
(* 0x88e20: ret *)
prreg HS (1%bv : bv 5) F1. prreg HS (10%bv : bv 5) F10.
lazymatch goal with Hfr5 : frame_of E _ (mrestrict _ _) (mrestrict _ _) |- _ =>
pose proof (kept_of_frame (segs := SEGS) _ _ _ _ _ (fun a => (res + c <= a < res + c + 1) \/ (outp <= a < outp + 8)) Hfr5
  ltac:(intros b wlo whi a Hin Hrr; vm_compute in Hin;
    repeat (destruct Hin as [Hq | Hin]; [injection Hq as <- <- <-; cbn [base_val] in Hrr; rewrite ?U46, ?U47, ?Usp in Hrr; lia|]); destruct Hin)) as UN end.
lazymatch type of HS with st_ok_pi _ _ ?Ef ?ssx (restrict _ ?msx) =>
  let r1 := eval vm_compute in (nth 1 (ss_mem ssx) got_regionP) in
  let r2 := eval vm_compute in (nth 2 (ss_mem ssx) got_regionP) in
  pose proof (st_ok_pi_region_nth Ef ssx (restrict _ msx) 1 r1 HS ltac:(vm_compute; reflexivity)) as RQ;
  pose proof (st_ok_pi_region_nth Ef ssx (restrict _ msx) 2 r2 HS ltac:(vm_compute; reflexivity)) as RO;
  cbn [ms_mem restrict] in RQ, RO end.
pose proof (field_of_region_any _ _ _ _ _ _ _ _ _ 0 1%N (SLit 0) RQ ltac:(cbn [ew ewset Nat.eqb]; exact U46) ltac:(left; reflexivity) ltac:(cbn; lia)) as VQ.
pose proof (field_of_region_any _ _ _ _ _ _ _ _ _ 0 8%N (SOff 23 0) RO ltac:(cbn [ew ewset Nat.eqb]; exact U47) ltac:(left; reflexivity) ltac:(cbn; lia)) as VO.
cbn [sv_denot ew ewset Nat.eqb] in VQ, VO.
rewrite (EE 23%nat 23%bv eq_refl), R23, !Z.add_0_r, Z_to_bv_bv_unsigned in VO. rewrite !Z.add_0_r in VQ.
rewrite unsigned_lit_small in VQ by lia. rewrite unsigned_lit_small in VO by lia.
change (2 ^ (8 * Z.of_N 1)) with 256 in VQ. change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64) in VO.
rewrite Z.mod_0_l in VQ by lia. rewrite Z.mod_small in VO by lia.
apply jw_aval_of_val in VQ. apply jw_aval_of_val in VO.
eapply (RET Wc _ _ _ _ _ HS eq_refl ltac:(vm_compute; reflexivity)).
intros mat'. unfold JPOST, apost_base.
lazymatch goal with |- exists _ _ _ _ _, mkCfg (mkst ?r _ ?m _) ?d = _ /\ _ => exists lyc, Sc, r, m, d end.
split.
{ rewrite F1, (EXn 33%nat ltac:(lia)). cbn [xF vsv nth map app j_saved Nat.sub]. replace (Z_to_bv 5 1) with (1%bv : bv 5) by (apply bv_eq; reflexivity).
  unfold YK0s.ret_ok in Hra0. rewrite Hra0. reflexivity. }
split; [apply (ajournal_materialize SEGS B LAWS pa_segs_low); exact HJ|].
split.
{ unfold aregs_preserved. intros r Hr.
  assert (Hcases : r = 2 \/ r = 3 \/ r = 4 \/ r = 8 \/ r = 9 \/ r = 18 \/ r = 19 \/ r = 20 \/ r = 21 \/ r = 22 \/ r = 23 \/
    r = 24 \/ r = 25 \/ r = 26 \/ r = 27 \/ False) by (unfold acallee_saved in Hr; lia).
  clear Hr.
  repeat (destruct Hcases as [-> | Hcases]); [..| destruct Hcases];
  rewrite (st_ok_pi_restrict_reg (w_H Wc) _ _ _ _ HS); cbn [ms_regs];
  lazymatch goal with |- sv_denot _ (sr_get ?a ?rr2) = _ => let v := eval vm_compute in (sr_get a rr2) in change (sr_get a rr2) with v end;
  cbn [sv_denot ew ewset Nat.eqb];
  first
  [ rewrite Z.add_0_r, Z_to_bv_bv_unsigned, EXn by lia; cbn [xF vsv nth map app j_saved Nat.sub]; reflexivity
  | replace (Z_to_bv 5 2) with (2%bv : bv 5) by (apply bv_eq; reflexivity); rewrite Usp; unfold spZ;
    replace (bv_unsigned (getr regs 2) - 128 + 128) with (bv_unsigned (getr regs 2)) by lia; apply Z_to_bv_bv_unsigned
  | rewrite Z.add_0_r, Z_to_bv_bv_unsigned, (EE 3%nat 3%bv eq_refl), R3;
    replace (Z_to_bv 5 3) with (3%bv : bv 5) by (apply bv_eq; reflexivity); rewrite Hgp0; reflexivity
  | rewrite Z.add_0_r, Z_to_bv_bv_unsigned, (EE 4%nat 4%bv eq_refl), R4;
    replace (Z_to_bv 5 4) with (4%bv : bv 5) by (apply bv_eq; reflexivity); rewrite Htp0; reflexivity ]. }
unfold JQ. exists res.
split; [rewrite F10, (EE 19%nat 19%bv eq_refl); exact R19|].
split; [lia|].
split; [rewrite Eab; unfold jtot; apply Permutation_sym, Permutation_cons_append|].
pose proof HJ as (HARf & _ & _ & _ & _ & _ & _ & _ & _ & F2f & _ & _ & Hgonef & _).
split.
{ apply Forall_forall. intros [b m] Hbm. cbn [fst snd].
  assert (Hbm3 : In (b, m) (ablocks B lyc Sc)) by (rewrite Eab; apply in_or_app; left; exact Hbm).
  destruct (al_blocks _ _ LAWS _ _ _ _ _ b m HAR Hbm3) as (_ & _ & _ & _ & _ & _ & Hm).
  pose proof (req_size_pos m (proj1 Hm)) as [Hm1 Hm2].
  apply in_split in Hbm as (l1 & l2 & El).
  pose proof (sep_blocks_pos SEGS B LAWS lyc Sc Wc _ _ (b, m) (res, jtot) l1 l2 [] HAR) as Hd.
  rewrite Eab, El, <- app_assoc in Hd. specialize (Hd eq_refl). unfold zdisjoint, block_rng in Hd. cbn [fst snd] in Hd.
  unfold iv_apart. unfold jtot in *. lia. }
split; [exists res, jtot; split; [exact Hres_in | unfold jtot; lia]|].
split.
{ intros i Hi. rewrite length_app in Hi. cbn [length] in Hi.
  destruct (Nat.lt_ge_cases i (length (join_sp ws))) as [Hlt | Hge].
  - rewrite app_nth1 by exact Hlt. rewrite UN by (unfold c in *; lia). exact (HBY i Hlt).
  - assert (i = length (join_sp ws)) as -> by lia. rewrite app_nth2 by lia. rewrite Nat.sub_diag. cbn [nth].
    pose proof (VQ 0%nat ltac:(lia)) as V0. rewrite Z.add_0_r in V0. fold c. rewrite V0. reflexivity. }
split; [exact VO|].
split.
{ intros p n i Hin Hi.
  assert (Hin' : In (p, n) (ablocks B lyc Sc)) by (rewrite Eab; apply in_or_app; left; exact Hin).
  destruct (al_blocks _ _ LAWS _ _ _ _ _ p n HAR Hin') as (_ & _ & Hpc & _ & _ & _ & Hm).
  pose proof (req_size_pos n (proj1 Hm)) as [Hn1 Hn2].
  apply (F2f p n i Hin Hin'); [lia | apply jw_nfp; lia]. }
split.
{ rewrite (blocks_bytes_bsum B lyc Sc), Eab, YCbq.bsum_app, <- (blocks_bytes_bsum B ly S).
  unfold LIVE_JOINED, jtot. cbn [YCbq.bsum fold_right snd]. lia. }
exact MLE.
Qed.
Lemma jw_val_of_aval : forall H m a (n : nat) v, aval_mem (aview SEGS H m) a n v -> val_mem SEGS (mrestrict H m) a n v.
Proof.
intros H m a n v Hv k Hk. pose proof (Hv k Hk) as H1. unfold aview in H1.
destruct (mbyte SEGS (mrestrict H m) (a + Z.of_nat k)) as [b|] eqn:Eb; [|discriminate].
cbn [option_map] in H1. injection H1 as H1. f_equal. unfold YO0f.le_byte, YG0f.le_byte in *. rewrite <- H1. symmetry. apply Z_to_bv_bv_unsigned.
Qed.
Lemma jw_hull_sub : forall (rd : reader) x n n', shadow_hull_vis rd x n -> 0 < n' <= n -> shadow_hull_vis rd x n'.
Proof.
intros rd x n n' H Hn s Hs. apply H. split; [lia|].
pose proof (shadow_mono (x + n' - 1) (x + n - 1) ltac:(lia)) as Hm.
assert (shadow_addr (x + n' - 1) / 8 * 8 <= shadow_addr (x + n - 1) / 8 * 8)
  by (apply Z.mul_le_mono_nonneg_r; [lia | apply Z.div_le_mono; lia]). lia.
Qed.
Lemma jw_rkept : forall E H (m m2 : word -> option byte) n b lo hi wlo whi cs,
bv_unsigned (ew E n) = b ->
(forall a, b + lo <= a < b + hi -> aview SEGS H m2 a = aview SEGS H m a) ->
(forall a, b + wlo <= a < b + whi -> apresent H m2 a) ->
region_kept SEGS E (mrestrict H m) (mrestrict H m2) (YP09.mkRegion (Some n) lo hi wlo whi cs).
Proof.
intros E H m m2 n b lo hi wlo whi cs Hn Hav Hp.
split; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi base_val]; rewrite Hn; intros a Ha.
- apply (mbyte_of_aview SEGS). apply Hav. exact Ha.
- intros _. apply (apresent_writable SEGS). apply Hp. exact Ha.
Qed.
Lemma jw_branch_lt : forall E a b x y, sv_denot E a = w64 x -> sv_denot E b = w64 y -> 0 <= x < 2 ^ 63 -> 0 <= y < 2 ^ 63 ->
branch_taken BC_LT (sv_denot E a) (sv_denot E b) = (x <? y).
Proof.
intros E a b x y Ha Hb Hx Hy. rewrite Ha, Hb. cbn [branch_taken]. rewrite bv_lts_signed.
unfold w64. rewrite !signed_of_small by (rewrite unsigned_lit_small by lia; unfold half64; lia).
rewrite !unsigned_lit_small by lia. reflexivity.
Qed.
Lemma jw_branch_ge : forall E a b x y, sv_denot E a = w64 x -> sv_denot E b = w64 y -> 0 <= x < 2 ^ 63 -> 0 <= y < 2 ^ 63 ->
branch_taken BC_GE (sv_denot E a) (sv_denot E b) = (y <=? x).
Proof.
intros E a b x y Ha Hb Hx Hy. rewrite Ha, Hb. cbn [branch_taken].
unfold w64. rewrite ?bv_lts_signed, ?bv_les_signed.
rewrite !signed_of_small by (rewrite unsigned_lit_small by lia; unfold half64; lia).
rewrite !unsigned_lit_small by lia.
destruct (Z.leb_spec y x); destruct (Z.ltb_spec x y); destruct (Z.leb_spec x y); destruct (Z.ltb_spec y x); try reflexivity; lia.
Qed.
Lemma jw_add_comm : forall a b : word, alu64 ALU_ADD a b = alu64 ALU_ADD b a.
Proof.
intros a b. rewrite <- (Z_to_bv_bv_unsigned _ a), <- (Z_to_bv_bv_unsigned _ b).
rewrite !zalu64_sound. unfold zalu64. cbn [zalu_raw]. f_equal. f_equal. lia.
Qed.
(* the unsigned branch the UBSan wrap checks of w->w + 8i take (0x88bf0, 0x88cb8, 0x88d2c): it is the walk's seeded
   condition, since the two pointers are different atoms *)
Lemma jw_branch_geu : forall E a b x y, sv_denot E a = w64 x -> sv_denot E b = w64 y -> 0 <= x < 2 ^ 64 -> 0 <= y < 2 ^ 64 ->
branch_taken BC_GEU (sv_denot E a) (sv_denot E b) = (y <=? x).
Proof.
intros E a b x y Ha Hb Hx Hy. rewrite branch_geu_U. unfold U. rewrite Ha, Hb.
unfold w64. rewrite !unsigned_lit_small by lia.
destruct (Z.leb_spec y x); destruct (Z.ltb_spec x y); try reflexivity; lia.
Qed.
(* `srli rd,rs,3` on a pointer atom: the shadow index before the shadow base is added (0x88bbc, 0x88c54) *)
Lemma jw_srl3 : forall (E : env) n c v, ew E n = Z_to_bv 64 v -> 0 <= v -> 0 <= c -> v + c < 2 ^ 63 ->
sv_denot E (SAlu ALU_SRL (SOff n c) (SLit 3)) = Z_to_bv 64 ((v + c) / 8).
Proof.
intros E n c v Hn Hv Hc0 Hc.
rewrite <- (Z_to_bv_bv_unsigned 64 (sv_denot E (SAlu ALU_SRL (SOff n c) (SLit 3)))). f_equal.
change (U E (SAlu ALU_SRL (SOff n c) (SLit 3)) = (v + c) / 8).
rewrite U_SAlu. cbn [zalu_raw]. rewrite U_SOff, Hn. rewrite unsigned_lit_small by lia.
change (Z.land (U E (SLit 3)) 63) with 3.
assert (Hd1 : 0 <= (v + c) / 8) by (apply Z.div_pos; lia).
assert (Hd2 : (v + c) / 8 <= v + c) by (apply Z.div_le_upper_bound; lia).
rewrite (zcanon_small (v + c)) by lia.
rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 3) with 8.
apply zcanon_small. lia.
Qed.
Lemma jw_land_ones64 : forall v, 0 <= v < 2 ^ 64 -> Z.land (2 ^ 64 - 1) v = v.
Proof.
intros v Hv. rewrite Z.land_comm.
replace (2 ^ 64 - 1) with (Z.ones 64) by (rewrite Z.ones_equiv; lia).
rewrite Z.land_ones by lia. apply Z.mod_small. exact Hv.
Qed.
(* `sgtz a0,a1; neg a0,a0; and s7,a0,a1` (0x88bd8 .. 0x88be0): max(n, 0) = n for a positive 32-bit count *)
Lemma jw_sgtz_and : forall (E : env) n v, ew E n = Z_to_bv 64 v -> 0 < v < 2 ^ 31 ->
sv_denot E (SAlu ALU_AND (SAlu ALU_SUB (SLit 0) (SAlu ALU_SLT (SLit 0) (SOff n 0))) (SOff n 0)) = Z_to_bv 64 v.
Proof.
intros E n v Hn Hv.
rewrite <- (Z_to_bv_bv_unsigned 64 (sv_denot E (SAlu ALU_AND (SAlu ALU_SUB (SLit 0) (SAlu ALU_SLT (SLit 0) (SOff n 0))) (SOff n 0)))). f_equal.
change (U E (SAlu ALU_AND (SAlu ALU_SUB (SLit 0) (SAlu ALU_SLT (SLit 0) (SOff n 0))) (SOff n 0)) = v).
assert (Uv : U E (SOff n 0) = v).
{ rewrite U_SOff, Hn, unsigned_lit_small by lia. rewrite Z.add_0_r. apply zcanon_small. lia. }
assert (Uslt : U E (SAlu ALU_SLT (SLit 0) (SOff n 0)) = 1).
{ rewrite U_SAlu. cbn [zalu_raw]. rewrite U_SLit, Uv.
  change (bv_swrap 64 (zcanon 0)) with 0.
  rewrite (bv_swrap_small 64 v) by (change (bv_half_modulus 64) with (2 ^ 63); lia).
  replace (0 <? v) with true by (symmetry; apply Z.ltb_lt; lia). apply zcanon_small. lia. }
assert (Usub : U E (SAlu ALU_SUB (SLit 0) (SAlu ALU_SLT (SLit 0) (SOff n 0))) = 2 ^ 64 - 1).
{ rewrite U_SAlu. cbn [zalu_raw]. rewrite U_SLit, Uslt. change (zcanon 0) with 0.
  unfold zcanon, M64. reflexivity. }
rewrite U_SAlu. cbn [zalu_raw]. rewrite Usub, Uv, jw_land_ones64 by lia. apply zcanon_small. lia.
Qed.
(* `not s10,s3` (0x88c84): the UBSan bound ~res of the fresh block *)
Lemma jw_den_not : forall (E : env) m v x, ew E m = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 ->
Z_to_bv 64 x = Z_to_bv 64 (-1) ->
sv_denot E (SAlu ALU_XOR (SOff m 0) (SLit x)) = Z_to_bv 64 (2 ^ 64 - 1 - v).
Proof.
intros E m v x Hm Hv Hx. cbn [sv_denot]. rewrite Hm, Hx. rewrite unsigned_lit_small by lia. rewrite Z.add_0_r.
apply bv_eq. rewrite alu64_unsigned. cbn [zalu_raw]. rewrite !Z_to_bv_unsigned.
unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64). rewrite (Z.mod_small v) by lia.
change ((-1) mod 2 ^ 64) with (2 ^ 64 - 1). rewrite YI08.lxor_allones by lia. reflexivity.
Qed.
(* the cursor of loop B before word i, and the separator it writes before word i *)
Definition jcur (i : nat) : Z := Z.of_nat (length (join_sp (firstn i ws))).
Definition jsep (i : nat) : list byte := if (i =? 0)%nat then [] else [SPACE].
Lemma jw_cur_S : forall i, (i < length ws)%nat ->
jcur (Datatypes.S i) = jcur i + Z.of_nat (length (jsep i)) + Z.of_nat (length (nth i ws [])) /\
join_sp (firstn (Datatypes.S i) ws) = (join_sp (firstn i ws) ++ jsep i) ++ nth i ws [] /\
jcur (Datatypes.S i) + 1 <= jtot.
Proof.
intros i Hi. unfold jcur, jsep. rewrite (jw_sp_S ws i Hi). split; [|split].
- rewrite !length_app. destruct (i =? 0)%nat; cbn [length]; lia.
- rewrite app_assoc. reflexivity.
- rewrite <- (jw_sp_S ws i Hi). pose proof (jw_len_sp_le (firstn (Datatypes.S i) ws)). pose proof (jw_need_firstn ws (Datatypes.S i)).
  unfold jtot. lia.
Qed.
(* the state at the head of loop B (0x88c9c) before word i: s0 holds the separator byte 32, s3 the block, s7 the
   cursor, s8 8i, s9 i, s10 ~res (the UBSan bound) and s11 the shadow index of &w->w *)
Definition LB (i : nat) lyc Sc (Wc : world SEGS) (rB : bvmap 5 word) mB dB res : Prop :=
ajournal SEGS B JOINED_STK sp0 FPj ly S W mem md [] lyc Sc Wc mB dB 1 /\
ablocks B lyc Sc = ablocks B ly S ++ [(res, jtot)] /\ 4096 <= res /\ mo_le MT S Sc (XM_JOINED MT ws) /\
jframe (mrestrict (w_H Wc) mB) /\ (forall j, 0 <= j < 8 -> apresent (w_H Wc) mB (outp + j)) /\
abytes_atR (rdW Wc mB) res (join_sp (firstn i ws)) /\
getr rB 2 = w64 (sp0 - 128) /\ getr rB 3 = w64 (as_gp B) /\ getr rB 4 = w64 (as_tp B) /\ getr rB 8 = w64 32 /\
getr rB 9 = w64 (W0 + 24) /\ getr rB 18 = w64 (W0 + 16) /\ getr rB 19 = w64 res /\ getr rB 21 = w64 SHADOW_OFF /\
getr rB 22 = w64 (SHADOW_OFF + (W0 + 24) / 8) /\ getr rB 23 = w64 (jcur i) /\ getr rB 24 = w64 (8 * Z.of_nat i) /\
getr rB 25 = w64 (Z.of_nat i) /\ getr rB 26 = w64 (2 ^ 64 - 1 - res) /\ getr rB 27 = w64 (SHADOW_OFF + (W0 + 16) / 8).
(* the facts a loop-B state carries, moved to a memory that keeps the frame, the bytes written so far and *len *)
Lemma jw_tr : forall (H : word -> bool) (m m' : word -> option byte) res (bs : list byte),
(forall a, sp0 - 112 <= a < sp0 -> aview SEGS H m' a = aview SEGS H m a) ->
(forall j, 0 <= j < 8 -> apresent H m (outp + j) -> apresent H m' (outp + j)) ->
(forall a, res <= a < res + Z.of_nat (length bs) -> aview SEGS H m' a = aview SEGS H m a) ->
jframe (mrestrict H m) -> (forall j, 0 <= j < 8 -> apresent H m (outp + j)) -> abytes_atR (aview SEGS H m) res bs ->
jframe (mrestrict H m') /\ (forall j, 0 <= j < 8 -> apresent H m' (outp + j)) /\ abytes_atR (aview SEGS H m') res bs.
Proof.
intros H m m' res bs KF KP KB HF HP HBS. destruct HF as (HF1 & HF2). split; [|split].
- split.
  + intros j r Hj. apply (val_mem_kept SEGS H H m m'); [|exact (HF1 j r Hj)].
    assert (Hj13 : (j < 13)%nat) by (apply (proj1 (nth_error_Some j_saved j)); rewrite Hj; discriminate).
    intros k Hk8. apply KF. cbn in Hk8. lia.
  + apply (val_mem_kept SEGS H H m m'); [|exact HF2]. intros k Hk8. apply KF. cbn in Hk8. lia.
- intros j Hj. exact (KP j Hj (HP j Hj)).
- intros j Hj. rewrite KB by lia. exact (HBS j Hj).
Qed.
Lemma jw_preg : forall r1 r2 (r : bv 5), aregs_preserved r1 r2 -> acallee_saved (bv_unsigned r) -> getr r2 r = getr r1 r.
Proof. intros r1 r2 r HP Hr. pose proof (HP (bv_unsigned r) Hr) as H. rewrite Z_to_bv_bv_unsigned in H. exact H. Qed.
Lemma jw_frame_kept : forall H H' (m m' : word -> option byte),
jframe (mrestrict H m) -> (forall a, sp0 - 112 <= a < sp0 -> aview SEGS H' m' a = aview SEGS H m a) -> jframe (mrestrict H' m').
Proof.
intros H H' m m' HF Hk. destruct HF as (HF1 & HF2). split.
- intros j r Hj. apply (val_mem_kept SEGS H H' m m'); [|exact (HF1 j r Hj)].
  assert (Hj13 : (j < 13)%nat) by (apply (proj1 (nth_error_Some j_saved j)); rewrite Hj; discriminate).
  intros k Hk8. apply Hk. cbn in Hk8. lia.
- apply (val_mem_kept SEGS H H' m m'); [|exact HF2]. intros k Hk8. apply Hk. cbn in Hk8. lia.
Qed.
(* the memcpy call of loop B (0x88d5c) and the rest of the iteration, 0x88d60 .. the branch back to the head (the
   block-wrap check 0x88d98 on the exit path is decided by the seed's facts) *)
Lemma jw_C : forall i lyc Sc Wc rT mT dT res,
(i < length ws)%nat ->
(forall lyc' Sc' Wc' rB mB dB, (Datatypes.S i < length ws)%nat -> LB (Datatypes.S i) lyc' Sc' Wc' rB mB dB res ->
  SRr SEGS Wc' (mkCfg (mkst rB (Z_to_bv 64 (BASE + PC_B)) mB (seg_rom SEGS)) dB) JPOST) ->
ajournal SEGS B JOINED_STK sp0 FPj ly S W mem md [] lyc Sc Wc mT dT 1 ->
ablocks B lyc Sc = ablocks B ly S ++ [(res, jtot)] -> 4096 <= res -> mo_le MT S Sc (XM_JOINED MT ws) ->
jframe (mrestrict (w_H Wc) mT) -> (forall j, 0 <= j < 8 -> apresent (w_H Wc) mT (outp + j)) ->
abytes_atR (rdW Wc mT) res (join_sp (firstn i ws) ++ jsep i) ->
getr rT 1 = w64 (BASE + 10288) -> getr rT 2 = w64 (sp0 - 128) -> getr rT 3 = w64 (as_gp B) -> getr rT 4 = w64 (as_tp B) ->
getr rT 8 = w64 32 -> getr rT 9 = w64 (W0 + 24) -> getr rT 18 = w64 (W0 + 16) -> getr rT 19 = w64 res ->
getr rT 20 = w64 (Z.of_nat (length (nth i ws []))) -> getr rT 21 = w64 SHADOW_OFF ->
getr rT 22 = w64 (SHADOW_OFF + (W0 + 24) / 8) ->
getr rT 10 = w64 (res + (jcur i + Z.of_nat (length (jsep i)))) -> getr rT 11 = w64 (nth i wp 0) ->
getr rT 12 = w64 (Z.of_nat (length (nth i ws []))) ->
getr rT 23 = w64 (jcur i + Z.of_nat (length (jsep i))) -> getr rT 24 = w64 (8 * Z.of_nat i) ->
getr rT 25 = w64 (Z.of_nat i) -> getr rT 26 = w64 (2 ^ 64 - 1 - res) -> getr rT 27 = w64 (SHADOW_OFF + (W0 + 16) / 8) ->
SRr SEGS Wc (mkCfg (mkst rT (Z_to_bv 64 (SIG CS___asan_memcpy)) mT (seg_rom SEGS)) dT) JPOST.
Proof.
intros i lyc Sc Wc rT mT dT res Hi IH HJ Eab Hres MLE HFR HOP HBY R1 R2 R3 R4 R8 R9 R18 R19 R20 R21 R22 R10 R11 R12 R23 R24 R25 R26 R27.
jctx.
destruct (jw_cur_S i Hi) as (EC & ESP & HCB).
set (c := jcur i) in *. set (dl := Z.of_nat (length (jsep i))) in *. set (len := Z.of_nat (length (nth i ws []))) in *.
assert (Hdl : 0 <= dl <= 1) by (unfold dl, jsep; destruct (i =? 0)%nat; cbn [length]; lia).
assert (Hc0 : 0 <= c) by (unfold c, jcur; lia).
pose proof HJ as (HAR & Hly & _ & _ & _ & Hfrs & _).
destruct (jw_ly _ _ _ _ _ _ HJ) as (Elo & Ehi & Etop).
assert (Hres_in : In (res, jtot) (ablocks B lyc Sc)) by (rewrite Eab; apply in_or_app; right; left; reflexivity).
destruct (al_blocks _ _ LAWS _ _ _ _ _ res jtot HAR Hres_in) as (Hr16 & Hr4096 & Hrceil & Hrapp & Hrpres & _ & Hrm).
pose proof (req_size_pos jtot ltac:(unfold jtot; pose proof (jw_need_nonneg ws); lia)) as [Hq1 Hq2].
destruct (jw_word i lyc Sc Wc mT dT 1 Hi HJ) as (Hp4096 & Hpceil & HLM & Hstr & HRD & _ & Hzone).
set (p := nth i wp 0) in *.
assert (HspT : spZ rT = sp0 + -128) by (unfold spZ at 1; rewrite R2; unfold w64; rewrite unsigned_lit_small by lia; lia).
assert (Hlen0 : 0 <= len) by (unfold len; lia).
(* the cursor at the memcpy call is below the block's size, so below MALLOC_MAX: atom 23's seeded range *)
assert (Hcd : 0 <= c + dl <= MALLOC_MAX).
{ pose proof HNEED as HMX. unfold jtot in HCB. unfold MALLOC_MAX in *. lia. }
pose proof (HRD rT ESTACK ltac:(rewrite HspT, Hes; lia)) as (Hx0 & Hxn & Hn32 & Hvis & Hamrx & Hrax & Hhx).
assert (Hdisj : res + jtot <= p \/ p + len + 1 <= res).
{ destruct Hzone as [(b & m & Hbm & Hb1 & Hb2) | Himg].
  - destruct (al_blocks _ _ LAWS _ _ _ _ _ b m HAR0 Hbm) as (_ & _ & _ & _ & _ & _ & Hm).
    pose proof (req_size_pos m (proj1 Hm)) as [Hm1 Hm2].
    apply in_split in Hbm as (l1 & l2 & El).
    pose proof (sep_blocks_pos SEGS B LAWS lyc Sc Wc _ _ (b, m) (res, jtot) l1 l2 [] HAR) as Hd.
    rewrite Eab, El, <- app_assoc in Hd. specialize (Hd eq_refl). unfold zdisjoint, block_rng in Hd. cbn [fst snd] in Hd. lia.
  - pose proof (blk_off_imgP B lyc Sc Wc _ _ res jtot HAR Hres_in) as Hoff. unfold off_img in Hoff. lia. }
eapply SRr_bind.
{ eapply (aj_intrin_atS SEGS B LAWS pa_segs_low OCpy (SIG CS___asan_memcpy) (AMEMCPY fx) Wc rT mT JOINED_STK sp0 FPj ly S W mem md []
    lyc Sc dT 1 (res + (c + dl)) p len (-128) (Z_to_bv 64 (BASE + 10288)) HJ).
  - exact R10. - exact R11. - exact R12. - lia. - lia. - lia.
  - exact HspT. - reflexivity. - lia. - rewrite Hes, HJS; lia.
  - exact R3. - exact R4. - exact R1. - apply ret_ok_codeptr_v; [lia | reflexivity].
  - intros a Ha. split; [|lia].
    replace a with (res + (a - res)) by lia.
    eapply (awr_new_block_any SEGS B LAWS); [exact (ajournal_init SEGS B JOINED_STK FPj ly S W regs mem md ch HPRE) | exact HAR | exact Eab
      | unfold jtot; pose proof (jw_need_nonneg ws); lia | exact Hres_in | lia].
  - intros a Ha Hf. exfalso. exact (jw_nfp a ltac:(lia) Hf).
  - apply (amem_range_of_block SEGS B LAWS lyc Sc Wc mT dT res jtot); [exact HAR | exact Hres_in | lia | lia].
  - apply (range_addressable_of_block SEGS B LAWS lyc Sc Wc mT dT res jtot); [exact HAR | exact Hres_in | lia | lia].
  - intros Hn0. apply (shadow_hull_vis_of_block SEGS B LAWS lyc Sc Wc mT dT res jtot); [exact HAR | exact Hres_in | lia | lia | lia].
  - split; [lia|]. split; [lia|]. split.
    { intros a Ha. destruct (Hvis a ltac:(lia)) as [Hv Hns]. split; [exact Hv | exact Hns]. }
    split; [lia|]. split; [unfold amem_range in *; lia|].
    split; [apply (range_addressable_sub _ _ p (len + 1)); [exact Hrax | lia | lia]|].
    intros Hn0. apply (jw_hull_sub _ p (len + 1)); [exact (Hhx ltac:(lia)) | lia]. }
cbv beta. intros W4 c4 _ (-> & regs4 & mem4 & md4 & -> & HJ4 & HP4 & Ha04 & Heff & Hfr4 & Hpres4 & HSM4).
(* back at 0x88d60: the symbolic state ssC from the registers the call kept *)
assert (Q2 : getr regs4 2 = w64 (sp0 - 128)) by (replace (2%bv : bv 5) with (Z_to_bv 5 2) by (apply bv_eq; reflexivity); rewrite (HP4 2 ltac:(unfold acallee_saved; lia)); replace (Z_to_bv 5 2) with (2%bv : bv 5) by (apply bv_eq; reflexivity); exact R2).
assert (Q3 : getr regs4 3 = w64 (as_gp B)) by (replace (3%bv : bv 5) with (Z_to_bv 5 3) by (apply bv_eq; reflexivity); rewrite (HP4 3 ltac:(unfold acallee_saved; lia)); replace (Z_to_bv 5 3) with (3%bv : bv 5) by (apply bv_eq; reflexivity); exact R3).
assert (Q4 : getr regs4 4 = w64 (as_tp B)) by (replace (4%bv : bv 5) with (Z_to_bv 5 4) by (apply bv_eq; reflexivity); rewrite (HP4 4 ltac:(unfold acallee_saved; lia)); replace (Z_to_bv 5 4) with (4%bv : bv 5) by (apply bv_eq; reflexivity); exact R4).
assert (Q8 : getr regs4 8 = w64 32) by (replace (8%bv : bv 5) with (Z_to_bv 5 8) by (apply bv_eq; reflexivity); rewrite (HP4 8 ltac:(unfold acallee_saved; lia)); replace (Z_to_bv 5 8) with (8%bv : bv 5) by (apply bv_eq; reflexivity); exact R8).
assert (Q9 : getr regs4 9 = w64 (W0 + 24)) by (replace (9%bv : bv 5) with (Z_to_bv 5 9) by (apply bv_eq; reflexivity); rewrite (HP4 9 ltac:(unfold acallee_saved; lia)); replace (Z_to_bv 5 9) with (9%bv : bv 5) by (apply bv_eq; reflexivity); exact R9).
assert (Q18 : getr regs4 18 = w64 (W0 + 16)) by (replace (18%bv : bv 5) with (Z_to_bv 5 18) by (apply bv_eq; reflexivity); rewrite (HP4 18 ltac:(unfold acallee_saved; lia)); replace (Z_to_bv 5 18) with (18%bv : bv 5) by (apply bv_eq; reflexivity); exact R18).
assert (Q19 : getr regs4 19 = w64 res) by (replace (19%bv : bv 5) with (Z_to_bv 5 19) by (apply bv_eq; reflexivity); rewrite (HP4 19 ltac:(unfold acallee_saved; lia)); replace (Z_to_bv 5 19) with (19%bv : bv 5) by (apply bv_eq; reflexivity); exact R19).
assert (Q20 : getr regs4 20 = w64 len) by (replace (20%bv : bv 5) with (Z_to_bv 5 20) by (apply bv_eq; reflexivity); rewrite (HP4 20 ltac:(unfold acallee_saved; lia)); replace (Z_to_bv 5 20) with (20%bv : bv 5) by (apply bv_eq; reflexivity); exact R20).
assert (Q21 : getr regs4 21 = w64 SHADOW_OFF) by (replace (21%bv : bv 5) with (Z_to_bv 5 21) by (apply bv_eq; reflexivity); rewrite (HP4 21 ltac:(unfold acallee_saved; lia)); replace (Z_to_bv 5 21) with (21%bv : bv 5) by (apply bv_eq; reflexivity); exact R21).
assert (Q22 : getr regs4 22 = w64 (SHADOW_OFF + (W0 + 24) / 8)) by (replace (22%bv : bv 5) with (Z_to_bv 5 22) by (apply bv_eq; reflexivity); rewrite (HP4 22 ltac:(unfold acallee_saved; lia)); replace (Z_to_bv 5 22) with (22%bv : bv 5) by (apply bv_eq; reflexivity); exact R22).
assert (Q23 : getr regs4 23 = w64 (c + dl)) by (replace (23%bv : bv 5) with (Z_to_bv 5 23) by (apply bv_eq; reflexivity); rewrite (HP4 23 ltac:(unfold acallee_saved; lia)); replace (Z_to_bv 5 23) with (23%bv : bv 5) by (apply bv_eq; reflexivity); exact R23).
assert (Q24 : getr regs4 24 = w64 (8 * Z.of_nat i)) by (replace (24%bv : bv 5) with (Z_to_bv 5 24) by (apply bv_eq; reflexivity); rewrite (HP4 24 ltac:(unfold acallee_saved; lia)); replace (Z_to_bv 5 24) with (24%bv : bv 5) by (apply bv_eq; reflexivity); exact R24).
assert (Q25 : getr regs4 25 = w64 (Z.of_nat i)) by (replace (25%bv : bv 5) with (Z_to_bv 5 25) by (apply bv_eq; reflexivity); rewrite (HP4 25 ltac:(unfold acallee_saved; lia)); replace (Z_to_bv 5 25) with (25%bv : bv 5) by (apply bv_eq; reflexivity); exact R25).
assert (Q26 : getr regs4 26 = w64 (2 ^ 64 - 1 - res)) by (replace (26%bv : bv 5) with (Z_to_bv 5 26) by (apply bv_eq; reflexivity); rewrite (HP4 26 ltac:(unfold acallee_saved; lia)); replace (Z_to_bv 5 26) with (26%bv : bv 5) by (apply bv_eq; reflexivity); exact R26).
assert (Q27 : getr regs4 27 = w64 (SHADOW_OFF + (W0 + 16) / 8)) by (replace (27%bv : bv 5) with (Z_to_bv 5 27) by (apply bv_eq; reflexivity); rewrite (HP4 27 ltac:(unfold acallee_saved; lia)); replace (Z_to_bv 5 27) with (27%bv : bv 5) by (apply bv_eq; reflexivity); exact R27).
destruct (jw_struct _ _ _ _ _ _ HJ4) as (SN & SA & SRA).
set (E := Eimg (Ereg regs4 [Z_to_bv 64 jSB; Z_to_bv 64 nW])).
assert (HEI : img_env VAL A_LIM E) by apply Eimg_env.
assert (EE : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E n = getr regs4 r)
  by (intros n r Hn; apply ew_Eimg_Ereg_nat; exact Hn).
assert (E32 : ew E 32 = Z_to_bv 64 jSB) by (unfold E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs4 _ 0)).
assert (E33 : ew E 33 = Z_to_bv 64 nW) by (unfold E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs4 _ 1)).
assert (U9 : bv_unsigned (ew E 9) = W0 + 24) by (rewrite (EE 9%nat 9%bv eq_refl), Q9; apply unsigned_lit_small; lia).
assert (HS : st_ok_pi SEGS VAL E ssC (restrict (w_H Wc) (mkst regs4 (Z_to_bv 64 (BASE + 10288)) mem4 (seg_rom SEGS)))).
{ rewrite restrict_mkst_fx. unfold ssC. apply pa_entry_st_ok_full.
  - change regsC with (sr_set (sr_set (sr_set sr_atoms 21 (SOff 32 0)) 22 (jshx 9)) 27 (jshx 18)).
    apply regs_ok_rereg; [apply regs_ok_rereg; [apply regs_ok_rereg; [apply regs_ok_Eimg_Ereg | reflexivity |] | reflexivity |] | reflexivity |].
    + cbn [sv_denot]. rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned. exact Q21.
    + unfold jshx. rewrite (denot_shx E 9 32 0 (W0 + 24) jSB) by (first [rewrite (EE 9%nat 9%bv eq_refl); exact Q9 | exact E32 | unfold jSB, SHADOW_OFF; lia | lia]).
      rewrite Q22. unfold jSB. rewrite Z.add_0_r. reflexivity.
    + unfold jshx. rewrite (denot_shx E 18 32 0 (W0 + 16) jSB) by (first [rewrite (EE 18%nat 18%bv eq_refl); exact Q18 | exact E32 | unfold jSB, SHADOW_OFF; lia | lia]).
      rewrite Q27. unfold jSB. rewrite Z.add_0_r. reflexivity.
  - vm_compute. reflexivity.
  - apply Forall_cons; [|apply Forall_nil]. unfold region_ok.
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val]. rewrite U9.
    split; [lia|]. split; [lia|]. split; [intros o Ho; lia|]. apply Forall_cons; [|apply Forall_nil].
    apply (chunk_ok_val SEGS E _ (W0 + 24) 0 4 (SOff 33 0) nW);
    [ cbn [sv_denot]; rewrite E33, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | cbn; lia | cbn; lia |].
    rewrite Z.add_0_r. exact (jw_val_of_aval _ _ _ _ _ SN).
  - apply pairwise_disjoint_of_extents. cbn. tauto.
  - split; [|split; exact I].
    cbn [f_atoms atoms_ok]. unfold afact_ok, jNOT. cbn [af_lo af_hi af_al2].
    rewrite U9, E32, E33.
    rewrite (EE 20%nat 20%bv eq_refl), Q20, (EE 23%nat 23%bv eq_refl), Q23, (EE 26%nat 26%bv eq_refl), Q26.
    unfold w64. rewrite !unsigned_lit_small by (unfold jSB, SHADOW_OFF, c, dl, jcur in *; lia).
    unfold jstklo, jstkhi8, jSB. rewrite Z.pow_0_r, !Z.mod_1_r.
    assert (0 < nW) by lia. repeat split; try exact I; unfold c, dl, jcur in *; lia. }
assert (SHOK : sh_ok SEGS jBx [] E (mrestrict (w_H Wc) mem4)) by apply Forall_nil.
assert (UB : U E jBx = SHADOW_OFF) by (unfold jBx; apply U_atom; [rewrite E32; reflexivity | unfold SHADOW_OFF; lia]).
paj_run_tok RUN HS HJ4 SHOK jBspan.
{ rewrite <- (aview_rd_of SEGS). rewrite UB, (U_atom E 9 (W0 + 24)) by (first [rewrite (EE 9%nat 9%bv eq_refl); exact Q9 | lia]).
  apply (range_addressable_sub _ _ (W0 + 16) 16); [exact SRA | lia | lia]. }
{ unfold ssC. cbn [ss_mem]. apply awr_ok_cons_ro; [cbn; lia|]. apply awr_ok_nil. }
(* the facts of the next head, at the memory after the run *)
lazymatch goal with Hfr5 : frame_of E _ (mrestrict _ _) (mrestrict _ _) |- _ =>
pose proof (kept_of_frame (segs := SEGS) _ _ _ _ _ (fun _ => False) Hfr5
  ltac:(intros b wlo whi a Hin Hrr; vm_compute in Hin;
    repeat (destruct Hin as [Hq | Hin]; [injection Hq as <- <- <-; cbn [base_val] in Hrr; lia|]); destruct Hin)) as UN end.
assert (K5 : forall a, sp0 - 112 <= a < sp0 -> rdW Wc (ms_mem ms) a = rdW Wc mT a).
{ intros a Ha. rewrite UN by (first [lia | tauto]). apply Hfr4; lia. }
assert (HFR5 : jframe (mrestrict (w_H Wc) (ms_mem ms))) by exact (jw_frame_kept _ _ _ _ HFR K5).
assert (HOP5 : forall j, 0 <= j < 8 -> apresent (w_H Wc) (ms_mem ms) (outp + j)).
{ intros j Hj. apply (apresent_grows (w_H Wc) mem4); [exact HG | apply Hpres4; exact (HOP j Hj)]. }
assert (HBY5 : abytes_atR (rdW Wc (ms_mem ms)) res (join_sp (firstn (Datatypes.S i) ws))).
{ rewrite ESP. intros j Hj. rewrite length_app in Hj.
  destruct (Nat.lt_ge_cases j (length (join_sp (firstn i ws) ++ jsep i))) as [Hlt | Hge].
  - assert (Hlt' : Z.of_nat j < c + dl) by (unfold c, dl, jcur; rewrite length_app in Hlt; lia).
    rewrite app_nth1 by exact Hlt. rewrite UN by (first [lia | tauto]).
    rewrite Hfr4 by lia. exact (HBY j Hlt).
  - rewrite app_nth2 by exact Hge.
    set (t := (j - length (join_sp (firstn i ws) ++ jsep i))%nat).
    assert (Ht : (t < length (nth i ws []))%nat) by (unfold t; lia).
    assert (Ej : res + Z.of_nat j = res + (c + dl) + Z.of_nat t) by (unfold t, c, dl, jcur; rewrite length_app in *; lia).
    rewrite Ej, UN by lia. rewrite (Heff (Z.of_nat t)) by (unfold len; lia).
    destruct Hstr as [Hb _]. rewrite (Hb t) by (rewrite length_app; cbn [length]; lia).
    rewrite app_nth1 by exact Ht. reflexivity. }
lazymatch type of HS with st_ok_pi _ _ _ _ (restrict _ ?m1) => clear UN; rename m1 into ms1 end.
psrr_branch_tok RUN BR HS SHOK jBspan.
- (* i + 1 < n: back to the head *)
  rewrite (jw_branch_lt _ _ _ (Z.of_nat i + 1) nW) in Hc;
    [| cbn [sv_denot ew ewset Nat.eqb]; rewrite (EE 25%nat 25%bv eq_refl), Q25; unfold w64; rewrite unsigned_lit_small by lia; reflexivity
     | cbn [sv_denot ew ewset Nat.eqb]; rewrite E33, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | lia | lia].
  apply Z.ltb_lt in Hc.
  paj_run_to_tok RUNTO HS HJ4 SHOK jBspan PC_B.
  { repeat (apply awr_ok_cons_ro; [cbn; lia|]). apply awr_ok_nil. }
  lazymatch goal with Hfr6 : frame_of _ _ (mrestrict _ _) (mrestrict _ _) |- _ =>
  pose proof (kept_of_frame (segs := SEGS) _ _ _ _ _ (fun _ => False) Hfr6
    ltac:(intros b wlo whi a Hin Hrr; vm_compute in Hin;
      repeat (destruct Hin as [Hq | Hin]; [injection Hq as <- <- <-; cbn [base_val] in Hrr; lia|]); destruct Hin)) as UN6 end.
  pmkst HS.
prreg HS (2%bv : bv 5) G2. prreg HS (3%bv : bv 5) G3. prreg HS (4%bv : bv 5) G4. prreg HS (8%bv : bv 5) G8.
prreg HS (9%bv : bv 5) G9. prreg HS (18%bv : bv 5) G18. prreg HS (19%bv : bv 5) G19. prreg HS (21%bv : bv 5) G21.
prreg HS (23%bv : bv 5) G23. prreg HS (24%bv : bv 5) G24. prreg HS (25%bv : bv 5) G25.
prreg HS (26%bv : bv 5) G26.
rewrite (EE 2%nat 2%bv eq_refl), Q2 in G2.
rewrite (EE 3%nat 3%bv eq_refl), Q3 in G3.
rewrite (EE 4%nat 4%bv eq_refl), Q4 in G4.
rewrite (EE 8%nat 8%bv eq_refl), Q8 in G8.
rewrite (EE 9%nat 9%bv eq_refl), Q9 in G9.
rewrite (EE 18%nat 18%bv eq_refl), Q18 in G18.
rewrite (EE 19%nat 19%bv eq_refl), Q19 in G19.
rewrite (EE 26%nat 26%bv eq_refl), Q26 in G26.
rewrite E32 in G21. change (Z_to_bv 64 jSB) with (w64 SHADOW_OFF) in G21.
rewrite (EE 20%nat 20%bv eq_refl), (EE 23%nat 23%bv eq_refl), Q20, Q23 in G23. unfold w64 in G23. rewrite alu_add_small in G23 by (unfold M64; lia).
rewrite (EE 24%nat 24%bv eq_refl), Q24 in G24. unfold w64 in G24. rewrite unsigned_lit_small in G24 by lia.
rewrite (EE 25%nat 25%bv eq_refl), Q25 in G25. unfold w64 in G25. rewrite unsigned_lit_small in G25 by lia.
assert (G22 : getr (ms_regs ms) 22 = w64 (SHADOW_OFF + (W0 + 24) / 8)).
{ jw_rawreg HS (22%bv : bv 5) H22.
  rewrite H22. rewrite (denot_shx _ 9 32 0 (W0 + 24) jSB); [unfold jSB; rewrite Z.add_0_r; reflexivity | cbn [ew ewset Nat.eqb]; rewrite (EE 9%nat 9%bv eq_refl); exact Q9
  | cbn [ew ewset Nat.eqb]; exact E32 | lia | lia | lia | unfold jSB, SHADOW_OFF; lia]. }
assert (G27 : getr (ms_regs ms) 27 = w64 (SHADOW_OFF + (W0 + 16) / 8)).
{ jw_rawreg HS (27%bv : bv 5) H27.
  rewrite H27. rewrite (denot_shx _ 18 32 0 (W0 + 16) jSB); [unfold jSB; rewrite Z.add_0_r; reflexivity | cbn [ew ewset Nat.eqb]; rewrite (EE 18%nat 18%bv eq_refl); exact Q18
  | cbn [ew ewset Nat.eqb]; exact E32 | lia | lia | lia | unfold jSB, SHADOW_OFF; lia]. }
  apply (IH lyc Sc Wc); [lia|].
  split; [exact HJ4|]. split; [exact Eab|]. split; [exact Hres|]. split; [exact MLE|].
  split; [apply (jw_frame_kept _ _ _ _ HFR5); intros a Ha; apply UN6; [lia | tauto]|].
  split; [intros j Hj; apply (apresent_grows (w_H Wc) (ms_mem ms1)); [assumption | exact (HOP5 j Hj)]|].
  split; [intros j Hj; assert (Hj' : Z.of_nat j < jcur (Datatypes.S i)) by (unfold jcur; lia);
    rewrite UN6 by (first [lia | tauto]); exact (HBY5 j Hj)|].
  split; [exact G2|]. split; [exact G3|]. split; [exact G4|]. split; [exact G8|]. split; [exact G9|].
  split; [exact G18|]. split; [exact G19|]. split; [exact G21|]. split; [exact G22|].
  split; [rewrite G23; unfold w64; f_equal; rewrite EC; unfold c, dl, len; lia|].
  split; [rewrite G24; unfold w64; f_equal; lia|].
  split; [rewrite G25; unfold w64; f_equal; lia|].
  split; [exact G26 | exact G27].
- (* i + 1 = n: on to the terminator *)
  rewrite (jw_branch_lt _ _ _ (Z.of_nat i + 1) nW) in Hc;
    [| cbn [sv_denot ew ewset Nat.eqb]; rewrite (EE 25%nat 25%bv eq_refl), Q25; unfold w64; rewrite unsigned_lit_small by lia; reflexivity
     | cbn [sv_denot ew ewset Nat.eqb]; rewrite E33, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | lia | lia].
  apply Z.ltb_ge in Hc.
  assert (Hall : firstn (Datatypes.S i) ws = ws) by (apply firstn_all2; lia).
  paj_run_to_tok RUNTO HS HJ4 SHOK jBspan PC_F.
  { repeat (apply awr_ok_cons_ro; [cbn; lia|]). apply awr_ok_nil. }
  lazymatch goal with Hfr6 : frame_of _ _ (mrestrict _ _) (mrestrict _ _) |- _ =>
  pose proof (kept_of_frame (segs := SEGS) _ _ _ _ _ (fun _ => False) Hfr6
    ltac:(intros b wlo whi a Hin Hrr; vm_compute in Hin;
      repeat (destruct Hin as [Hq | Hin]; [injection Hq as <- <- <-; cbn [base_val] in Hrr; lia|]); destruct Hin)) as UN6 end.
  pmkst HS.
prreg HS (2%bv : bv 5) G2. prreg HS (3%bv : bv 5) G3. prreg HS (4%bv : bv 5) G4.
prreg HS (10%bv : bv 5) G10. prreg HS (19%bv : bv 5) G19. prreg HS (21%bv : bv 5) G21. prreg HS (23%bv : bv 5) G23.
rewrite (EE 2%nat 2%bv eq_refl), Q2 in G2.
rewrite (EE 3%nat 3%bv eq_refl), Q3 in G3.
rewrite (EE 4%nat 4%bv eq_refl), Q4 in G4.
rewrite (EE 19%nat 19%bv eq_refl), Q19 in G19.
rewrite E32 in G21. change (Z_to_bv 64 jSB) with (w64 SHADOW_OFF) in G21.
rewrite (EE 20%nat 20%bv eq_refl), (EE 23%nat 23%bv eq_refl), Q20, Q23 in G23. unfold w64 in G23. rewrite alu_add_small in G23 by (unfold M64; lia).
rewrite (EE 19%nat 19%bv eq_refl), (EE 20%nat 20%bv eq_refl), (EE 23%nat 23%bv eq_refl), Q19, Q20, Q23 in G10.
unfold w64 in G10. rewrite !alu_add_small in G10 by (unfold M64; lia).
  apply (jw_final lyc Sc Wc (ms_regs ms) (ms_mem ms) _ res HJ4 Eab Hres MLE).
  + apply (jw_frame_kept _ _ _ _ HFR5). intros a Ha. apply UN6; [lia | tauto].
  + intros j Hj. apply (apresent_grows (w_H Wc) (ms_mem ms1)); [assumption | exact (HOP5 j Hj)].
  + rewrite Hall in HBY5. intros j Hj.
    assert (Hj' : Z.of_nat j < jcur (Datatypes.S i)) by (unfold jcur; rewrite Hall; lia).
    rewrite UN6 by (first [lia | tauto]). exact (HBY5 j Hj).
  + exact G2. + exact G3. + exact G4.
  + rewrite G10. unfold w64. f_equal. pose proof EC as EC'. unfold jcur in EC'. rewrite Hall in EC'. unfold c, dl, len. lia.
  + exact G19. + exact G21.
  + rewrite G23. unfold w64. f_equal. pose proof EC as EC'. unfold jcur in EC'. rewrite Hall in EC'. unfold c, dl, len. lia.
Qed.
(* loop B (0x88c9c .. 0x88d5c): the four UBSan checks of w->w + 8i (0x88cb4, 0x88cb8, 0x88cbc, 0x88cc8) and the two
   block-wrap checks (0x88cec, 0x88d0c), all decided by the seed's facts; word i's length by the strlen entry, the
   separator, then the memcpy of jw_C *)
Lemma jw_loopB : forall (k i : nat) lyc Sc Wc rB mB dB res,
(length ws - i <= k)%nat -> (i < length ws)%nat -> LB i lyc Sc Wc rB mB dB res ->
SRr SEGS Wc (mkCfg (mkst rB (Z_to_bv 64 (BASE + PC_B)) mB (seg_rom SEGS)) dB) JPOST.
Proof.
induction k as [|k IHk]; intros i lyc Sc Wc rB mB dB res Hk Hi HLB; [lia|].
destruct HLB as (HJ & Eab & Hres & MLE & HFR & HOP & HBY & R2 & R3 & R4 & R8 & R9 & R18 & R19 & R21 & R22 & R23 & R24 & R25 & R26 & R27).
jctx.
destruct (jw_cur_S i Hi) as (EC & ESP & HCB).
set (c := jcur i) in *. set (len := Z.of_nat (length (nth i ws []))) in *.
assert (Hc0 : 0 <= c) by (unfold c, jcur; lia).
pose proof HJ as (HAR & Hly & _ & _ & _ & Hfrs & _).
destruct (jw_ly _ _ _ _ _ _ HJ) as (Elo & Ehi & Etop).
assert (Hres_in : In (res, jtot) (ablocks B lyc Sc)) by (rewrite Eab; apply in_or_app; right; left; reflexivity).
destruct (al_blocks _ _ LAWS _ _ _ _ _ res jtot HAR Hres_in) as (Hr16 & Hr4096 & Hrceil & Hrapp & Hrpres & _ & Hrm).
pose proof (req_size_pos jtot ltac:(unfold jtot; pose proof (jw_need_nonneg ws); lia)) as [Hq1 Hq2].
destruct (jw_struct _ _ _ _ _ _ HJ) as (SN & SA & SRA).
destruct (jw_argv i _ _ _ _ _ _ Hi HJ) as (Hp1 & Hp2 & VP & RAP).
destruct (jw_word i _ _ _ _ _ _ Hi HJ) as (Hw1 & Hw2 & HLM & Hstr & HRD & HTV & Hzone).
set (p := arr + 8 * Z.of_nat i) in *. set (wpi := nth i wp 0) in *. set (q := res + c).
assert (Hpq : p + 8 <= res \/ res + jtot <= p).
{ destruct HAB as (b & m & Hbm & Hb1 & Hb2).
  destruct (al_blocks _ _ LAWS _ _ _ _ _ b m HAR0 Hbm) as (_ & _ & _ & _ & _ & _ & Hm).
  pose proof (req_size_pos m (proj1 Hm)) as [Hm1 Hm2].
  apply in_split in Hbm as (l1 & l2 & El).
  pose proof (sep_blocks_pos SEGS B LAWS lyc Sc Wc _ _ (b, m) (res, jtot) l1 l2 [] HAR) as Hd.
  rewrite Eab, El, <- app_assoc in Hd. specialize (Hd eq_refl). unfold zdisjoint, block_rng in Hd. cbn [fst snd] in Hd.
  unfold p. lia. }
assert (Hp8 : p mod 8 = 0).
{ unfold p. replace (arr + 8 * Z.of_nat i) with (arr + Z.of_nat i * 8) by lia. rewrite Z_mod_plus_full. exact HARR8. }
assert (Hlen0 : 0 <= len) by (unfold len; lia).
(* the cursor at the head of loop B is below the block's size, so below MALLOC_MAX: atom 23's seeded range *)
assert (Hcm : 0 <= c <= MALLOC_MAX).
{ pose proof HNEED as HMX. unfold jtot in HCB. unfold MALLOC_MAX in *. lia. }
(* the seed: atoms 32 SB, 33 arr, 34 n, 35 p = arr + 8i, 36 the word's pointer, 37 q = res + cursor *)
set (xB := [Z_to_bv 64 jSB; Z_to_bv 64 arr; Z_to_bv 64 nW; Z_to_bv 64 p; Z_to_bv 64 wpi; Z_to_bv 64 q]).
set (E := Eimg (Ereg rB xB)).
assert (HEI : img_env VAL A_LIM E) by apply Eimg_env.
assert (EE : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E n = getr rB r)
  by (intros n r Hn; apply ew_Eimg_Ereg_nat; exact Hn).
assert (EX : forall j, (j < 6)%nat -> ew E (32 + j) = nth j xB (Z_to_bv 64 0)).
{ intros j Hj. unfold E. rewrite Eimg_low by (unfold A_TEXT; lia). apply ew_Ereg_extra. }
assert (E32 : ew E 32 = Z_to_bv 64 jSB) by exact (EX 0%nat ltac:(lia)).
assert (E33 : ew E 33 = Z_to_bv 64 arr) by exact (EX 1%nat ltac:(lia)).
assert (E34 : ew E 34 = Z_to_bv 64 nW) by exact (EX 2%nat ltac:(lia)).
assert (E35 : ew E 35 = Z_to_bv 64 p) by exact (EX 3%nat ltac:(lia)).
assert (E36 : ew E 36 = Z_to_bv 64 wpi) by exact (EX 4%nat ltac:(lia)).
assert (E37 : ew E 37 = Z_to_bv 64 q) by exact (EX 5%nat ltac:(lia)).
assert (U9 : bv_unsigned (ew E 9) = W0 + 24) by (rewrite (EE 9%nat 9%bv eq_refl), R9; apply unsigned_lit_small; lia).
assert (U18 : bv_unsigned (ew E 18) = W0 + 16) by (rewrite (EE 18%nat 18%bv eq_refl), R18; apply unsigned_lit_small; lia).
assert (U19 : bv_unsigned (ew E 19) = res) by (rewrite (EE 19%nat 19%bv eq_refl), R19; apply unsigned_lit_small; lia).
assert (U35 : bv_unsigned (ew E 35) = p) by (rewrite E35; apply unsigned_lit_small; lia).
assert (U37 : bv_unsigned (ew E 37) = q) by (rewrite E37; apply unsigned_lit_small; unfold q; lia).
assert (Harr : 4096 <= arr) by (destruct HAB as (b & m & Hbm & Hb1 & _); destruct (al_blocks _ _ LAWS _ _ _ _ _ b m HAR0 Hbm) as (_ & Hb4 & _); lia).
assert (HS : st_ok_pi SEGS VAL E ssB (restrict (w_H Wc) (mkst rB (Z_to_bv 64 (BASE + PC_B)) mB (seg_rom SEGS)))).
{ rewrite restrict_mkst_fx. unfold ssB. apply pa_entry_st_ok_full.
  - change regsB with (sr_set (sr_set (sr_set (sr_set sr_atoms 27 (jshx 18)) 22 (jshx 9)) 21 (SOff 32 0)) 8 (SLit 32)).
    apply regs_ok_rereg; [apply regs_ok_rereg; [apply regs_ok_rereg; [apply regs_ok_rereg; [apply regs_ok_Eimg_Ereg | reflexivity |] | reflexivity |] | reflexivity |] | reflexivity |].
    + unfold jshx. rewrite (denot_shx E 18 32 0 (W0 + 16) jSB) by (first [rewrite (EE 18%nat 18%bv eq_refl); exact R18 | exact E32 | unfold jSB, SHADOW_OFF; lia | lia]).
      rewrite R27. unfold jSB. rewrite Z.add_0_r. reflexivity.
    + unfold jshx. rewrite (denot_shx E 9 32 0 (W0 + 24) jSB) by (first [rewrite (EE 9%nat 9%bv eq_refl); exact R9 | exact E32 | unfold jSB, SHADOW_OFF; lia | lia]).
      rewrite R22. unfold jSB. rewrite Z.add_0_r. reflexivity.
    + cbn [sv_denot]. rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned. exact R21.
    + cbn [sv_denot]. exact R8.
  - vm_compute. reflexivity.
  - repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
      cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
    + rewrite U18. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|]. apply Forall_cons; [|apply Forall_nil].
      apply (chunk_ok_val SEGS E _ (W0 + 16) 0 8 (SOff 33 0) arr);
      [ cbn [sv_denot]; rewrite E33, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | cbn; lia | cbn; lia |].
      rewrite Z.add_0_r. exact (jw_val_of_aval _ _ _ _ _ SA).
    + rewrite U9. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|]. apply Forall_cons; [|apply Forall_nil].
      apply (chunk_ok_val SEGS E _ (W0 + 24) 0 4 (SOff 34 0) nW);
      [ cbn [sv_denot]; rewrite E34, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | cbn; lia | cbn; lia |].
      rewrite Z.add_0_r. exact (jw_val_of_aval _ _ _ _ _ SN).
    + rewrite U35. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|]. apply Forall_cons; [|apply Forall_nil].
      apply (chunk_ok_val SEGS E _ p 0 8 (SOff 36 0) wpi);
      [ cbn [sv_denot]; rewrite E36, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | cbn; lia | cbn; lia |].
      rewrite Z.add_0_r. exact (jw_val_of_aval _ _ _ _ _ VP).
    + rewrite U37. split; [unfold q; lia|]. split; [unfold q; lia|]. split; [|constructor].
      intros o Ho. apply (apresent_writable SEGS). apply (proj1 (Hrpres (q + o) ltac:(unfold q; lia))).
  - apply pairwise_disjoint_of_extents. unfold extent_of_region.
    cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite U18, U9, U35, U37.
    cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd]. unfold q. repeat split; lia.
  - split; [|split].
    + cbn [f_atoms atoms_ok]. unfold afact_ok, jNOT. cbn [af_lo af_hi af_al2].
      rewrite U9, U18, U19, U35, U37, E32, E33, E34.
      rewrite !unsigned_lit_small by (unfold jSB, SHADOW_OFF; lia).
      rewrite (EE 23%nat 23%bv eq_refl), R23, (EE 26%nat 26%bv eq_refl), R26.
      unfold w64. rewrite !unsigned_lit_small by (unfold c, jcur in *; lia).
      unfold jstklo, jstkhi8, jheaphi, jSB, q. change (2 ^ 3) with 8. rewrite Z.pow_0_r, !Z.mod_1_r.
      repeat split; first [exact I | exact Hp8 | unfold c, jcur in *; lia].
    + cbn [f_conds conds_ok]. split; [|exact I].
      unfold acond_ok. cbn [ac_c ac_a ac_b].
      rewrite (jw_branch_geu E (SOff 35 0) (SOff 33 0) p arr);
        [ apply Z.leb_le; unfold p; lia
        | cbn [sv_denot]; rewrite E35, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
        | cbn [sv_denot]; rewrite E33, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
        | lia | lia].
    + cbn [f_alias alias_ok]. split; [|split; [|split; [|exact I]]].
      * cbn [sv_denot]. rewrite E33, (EE 24%nat 24%bv eq_refl), R24, E35, !Z.add_0_r, !Z_to_bv_bv_unsigned.
        unfold w64. rewrite alu_add_small by (unfold M64; lia). reflexivity.
      * cbn [sv_denot]. rewrite E33, (EE 24%nat 24%bv eq_refl), R24, E35, !Z.add_0_r, !Z_to_bv_bv_unsigned.
        unfold w64. rewrite jw_add_comm, alu_add_small by (unfold M64; lia). reflexivity.
      * cbn [sv_denot]. rewrite (EE 19%nat 19%bv eq_refl), (EE 23%nat 23%bv eq_refl), R19, R23, E37, !Z.add_0_r, !Z_to_bv_bv_unsigned.
        unfold w64. rewrite alu_add_small by (unfold M64; lia). reflexivity. }
assert (UB : U E jBx = SHADOW_OFF) by (unfold jBx; apply U_atom; [rewrite E32; reflexivity | unfold SHADOW_OFF; lia]).
assert (SHOK : sh_ok SEGS jBx SHB E (mrestrict (w_H Wc) mB)).
{ unfold sh_ok, SHB. apply Forall_cons; [|apply Forall_nil].
  unfold shent_ok, app_apart. cbn [she_m she_lo she_hi].
  assert (U37' : U E (SOff 37 0) = q) by (apply U_atom; [exact E37 | unfold q; lia]).
  rewrite UB, U37', <- (aview_rd_of SEGS). split.
  - apply (range_addressable_of_block SEGS B LAWS lyc Sc Wc mB dB res jtot); [exact HAR | exact Hres_in | unfold q; lia | unfold q; lia].
  - intros a Ha. destruct Hrapp as [_ [Hlow | [Hhi1 Hhi2]]]; unfold q, kLowShadowBeg, kHighMemBeg, SHADOW_OFF in *; lia. }
paj_run_tok RUN HS HJ SHOK jBspan.
{ rewrite <- (aview_rd_of SEGS). rewrite UB, (U_atom E 35 p) by (first [exact E35 | lia]). exact RAP. }
{ rewrite <- (aview_rd_of SEGS). rewrite UB, (U_atom E 18 (W0 + 16)) by (first [rewrite (EE 18%nat 18%bv eq_refl); exact R18 | lia]).
  apply (range_addressable_sub _ _ (W0 + 16) 16); [exact SRA | lia | lia]. }
{ unfold ssB. cbn [ss_mem].
  apply awr_ok_cons_ro; [cbn; lia|]. apply awr_ok_cons_ro; [cbn; lia|]. apply awr_ok_cons_ro; [cbn; lia|].
  eapply awr_ok_cons_gen; [reflexivity | exact U37 | |].
  { intros a Ha. cbn [YP09.r_wlo YP09.r_whi] in Ha. replace a with (res + c) by (unfold q in Ha; lia).
    eapply (awr_new_block_any SEGS B LAWS); [exact (ajournal_init SEGS B JOINED_STK FPj ly S W regs mem md ch HPRE) | exact HAR | exact Eab
      | unfold jtot; pose proof (jw_need_nonneg ws); lia | exact Hres_in | unfold jtot in *; lia]. }
  apply awr_ok_nil. }
(* 0x88ce0: the strlen entry on word i *)
lazymatch goal with Hfr : frame_of E _ (mrestrict _ _) (mrestrict _ _) |- _ =>
pose proof (kept_of_frame (segs := SEGS) _ _ _ _ _ (fun a => q <= a < q + 1) Hfr
  ltac:(intros b wlo whi a Hin Hrr; vm_compute in Hin;
    repeat (destruct Hin as [Hq | Hin]; [injection Hq as <- <- <-; cbn [base_val] in Hrr; rewrite ?U37, ?U35, ?U9, ?U18 in Hrr; lia|]); destruct Hin)) as UN1 end.
destruct (jw_tr (w_H Wc) mB (ms_mem ms) res (join_sp (firstn i ws))) as (HFR1 & HOP1 & HBY1);
  [ intros a Ha; apply UN1; [lia | unfold q; lia]
  | intros j Hj Ha; eapply apresent_grows; [eassumption | exact Ha]
  | intros a Ha; unfold q, c, jcur in *; apply UN1; lia | exact HFR | exact HOP | exact HBY |].
pmkst HS.
prreg HS (1%bv : bv 5) P1. prreg HS (2%bv : bv 5) P2. prreg HS (3%bv : bv 5) P3. prreg HS (4%bv : bv 5) P4. prreg HS (10%bv : bv 5) P10.
assert (HspT : spZ (ms_regs ms) = sp0 + -128).
{ unfold spZ at 1. rewrite P2, (EE 2%nat 2%bv eq_refl), R2. unfold w64. rewrite unsigned_lit_small by lia. lia. }
assert (P3' : getr (ms_regs ms) 3 = w64 (as_gp B)) by (rewrite P3, (EE 3%nat 3%bv eq_refl); exact R3).
assert (P4' : getr (ms_regs ms) 4 = w64 (as_tp B)) by (rewrite P4, (EE 4%nat 4%bv eq_refl); exact R4).
assert (P10' : getr (ms_regs ms) 10 = w64 wpi) by (rewrite P10, E36; reflexivity).
assert (HraT : YK0s.ret_ok (getr (ms_regs ms) 1)) by (rewrite P1; apply ret_ok_codeptr_v; [lia | reflexivity]).
destruct (jw_word i _ _ _ _ _ _ Hi HJ) as (_ & _ & _ & Hstr1 & HRD1 & HTV1 & _).
eapply SRr_bind.
{ eapply (jw_art_at ESTACK (fun _ => False) (SIG CS___interceptor_trampoline_strlen)
    Wc (ms_regs ms) (ms_mem ms) JOINED_STK sp0 FPj ly S W mem md [] lyc Sc _ 1 (-128) (Z_to_bv 64 (BASE + 10164)) _ HJ HspT eq_refl
    ltac:(lia) ltac:(lia) ltac:(rewrite Hes, HJS; lia) P1 (fun a (H : False) => False_ind _ H)).
  apply (ASTRLEN fx lyc Sc Wc (ms_regs ms) (ms_mem ms) _ wpi (nth i ws [])).
  - exact (ecall_pre_stk_at SEGS B ESTACK JOINED_STK sp0 FPj ly S W mem md [] lyc Sc Wc (ms_mem ms) _ 1 (ms_regs ms) (-128) HJ HspT eq_refl
      ltac:(lia) ltac:(lia) ltac:(rewrite Hes, HJS; lia) HraT P3' P4').
  - exact P10'.
  - lia.
  - apply (astr_atR_view SEGS). exact Hstr1.
  - apply HRD1. rewrite HspT, Hes. lia.
  - exact HTV1.
  - exact (jw_rom _ _ _ _ _ _ HJ). }
cbv beta. intros W2 c2 _ (-> & regs2 & mem2 & md2 & -> & HJ2 & HP2 & HQ2 & HK2 & HPR2).
jafter_call_keep_pi HS 40%nat regs2 (mrestrict (w_H Wc) mem2) HP2 [0;1;2;3]%nat HS2.
match type of HS2 with ?t -> _ => assert (HRK : t); [|specialize (HS2 HRK); clear HRK] end.
{ cbn [ms_mem restrict]. pose proof (proj1 HJ2) as HAR2.
  destruct (al_blocks _ _ LAWS _ _ _ _ _ res jtot HAR2 Hres_in) as (_ & _ & _ & _ & Hrpres2 & _).
  repeat apply Forall_cons; try apply Forall_nil;
  (eapply jw_rkept; [cbn [ew ewset Nat.eqb]; first [exact U18 | exact U9 | exact U35 | exact U37]
    | intros a Ha; apply HK2; [lia | rewrite Hes; unfold q in *; lia | tauto]
    | intros a Ha; first [lia | apply (proj1 (Hrpres2 a ltac:(unfold q in Ha; lia)))]]). }
destruct (jw_tr (w_H Wc) (ms_mem ms) mem2 res (join_sp (firstn i ws))) as (HFR2 & HOP2 & HBY2);
  [ intros a Ha; apply HK2; [lia | rewrite Hes; lia | tauto]
  | intros j Hj Ha; exact (HPR2 _ Ha)
  | intros a Ha; unfold c, jcur in *; apply HK2; [lia | rewrite Hes; lia | tauto] | exact HFR1 | exact HOP1 | exact HBY1 |].
clear HS. rewrite <- restrict_mkst_fx in HS2. rename HS2 into HS.
lazymatch type of HS with st_ok_pi _ _ ?E2t _ _ => remember E2t as E2 eqn:HE2 end.
assert (HEI2 : img_env VAL A_LIM E2) by (rewrite HE2; apply img_env_havoc; [assumption | cbv; lia]).
assert (OLD2 : forall n, (n < 40)%nat -> ew E2 n = ew E n).
{ intros n Hn. rewrite HE2, YN3v.ew_havoc_old by lia. repeat rewrite ew_ewset_other by lia. reflexivity. }
assert (E44 : ew E2 44 = getr regs2 10) by (rewrite HE2; reflexivity).
clear HE2.
assert (SHOK2 : sh_ok SEGS jBx SHB E2 (mrestrict (w_H Wc) mem2)).
{ unfold sh_ok, SHB. apply Forall_cons; [|apply Forall_nil].
  unfold shent_ok, app_apart. cbn [she_m she_lo she_hi].
  assert (U37' : U E2 (SOff 37 0) = q) by (apply U_atom; [rewrite OLD2 by lia; exact E37 | unfold q; lia]).
  assert (UB2 : U E2 jBx = SHADOW_OFF) by (unfold jBx; apply U_atom; [rewrite OLD2 by lia; rewrite E32; reflexivity | unfold SHADOW_OFF; lia]).
  rewrite UB2, U37', <- (aview_rd_of SEGS). split.
  - apply (range_addressable_of_block SEGS B LAWS lyc Sc Wc mem2 md2 res jtot); [exact (proj1 HJ2) | exact Hres_in | unfold q; lia | unfold q; lia].
  - intros a Ha. destruct Hrapp as [_ [Hlow | [Hhi1 Hhi2]]]; unfold q, kLowShadowBeg, kHighMemBeg, SHADOW_OFF in *; lia. }
(* 0x88ce4 .. 0x88ce8: s4 := the length; beqz s8 *)
paj_run_tok RUN HS HJ2 SHOK2 jBspan.
{ repeat (apply awr_ok_cons_ro; [cbn; lia|]).
  eapply awr_ok_cons_gen; [reflexivity | cbn [ew ewset Nat.eqb]; rewrite OLD2 by lia; exact U37 | |].
  { intros a Ha. cbn [YP09.r_wlo YP09.r_whi] in Ha. replace a with (res + c) by (unfold q in Ha; lia).
    eapply (awr_new_block_any SEGS B LAWS); [exact (ajournal_init SEGS B JOINED_STK FPj ly S W regs mem md ch HPRE) | exact (proj1 HJ2) | exact Eab
      | unfold jtot; pose proof (jw_need_nonneg ws); lia | exact Hres_in | unfold jtot in *; lia]. }
  apply awr_ok_nil. }
lazymatch type of HS with st_ok_pi _ _ _ _ (restrict _ ?mz) => rename mz into ms2 end.
lazymatch goal with Hfr : frame_of E2 _ (mrestrict _ _) (mrestrict _ _) |- _ =>
pose proof (kept_of_frame (segs := SEGS) _ _ _ _ _ (fun a => q <= a < q + 1) Hfr
  ltac:(intros b wlo whi a Hin Hrr; vm_compute in Hin;
    repeat (destruct Hin as [Hq | Hin]; [injection Hq as <- <- <-; cbn [base_val] in Hrr; rewrite ?OLD2 in Hrr by lia; rewrite ?U37, ?U35, ?U9, ?U18 in Hrr; lia|]); destruct Hin)) as UN2 end.
destruct (jw_tr (w_H Wc) mem2 (ms_mem ms2) res (join_sp (firstn i ws))) as (HFR3 & HOP3 & HBY3);
  [ intros a Ha; apply UN2; [lia | unfold q; lia]
  | intros j Hj Ha; eapply apresent_grows; [eassumption | exact Ha]
  | intros a Ha; unfold q, c, jcur in *; apply UN2; lia | exact HFR2 | exact HOP2 | exact HBY2 |].
psrr_branch_tok RUN BR HS SHOK2 jBspan.
- (* i = 0: no separator *)
  rewrite branch_eq_U, U_SLit in Hc. rewrite (U_atom _ 24 (8 * Z.of_nat i)) in Hc;
    [| cbn [ew ewset Nat.eqb]; rewrite OLD2 by lia; rewrite (EE 24%nat 24%bv eq_refl); exact R24 | lia].
  change (zcanon 0) with 0 in Hc. apply Z.eqb_eq in Hc. assert (i = 0%nat) as Hi0 by lia.
  paj_run_tok RUN HS HJ2 SHOK2 jBspan.
  { rewrite <- (aview_rd_of SEGS). destruct (jw_argv i _ _ _ _ _ _ Hi HJ2) as (_ & _ & _ & RAP2).
    rewrite (U_atom _ 32 SHADOW_OFF), (U_atom _ 35 p); [exact RAP2 | | | |]; cbn [ew ewset Nat.eqb]; rewrite ?OLD2 by lia;
    first [exact E35 | rewrite E32; reflexivity | unfold SHADOW_OFF; lia | lia]. }
  { rewrite <- (aview_rd_of SEGS). destruct (jw_struct _ _ _ _ _ _ HJ2) as (_ & _ & SRA2).
    rewrite (U_atom _ 32 SHADOW_OFF), (U_atom _ 18 (W0 + 16)); [apply (range_addressable_sub _ _ (W0 + 16) 16); [exact SRA2 | lia | lia] | | | |];
    cbn [ew ewset Nat.eqb]; rewrite ?OLD2 by lia; first [rewrite (EE 18%nat 18%bv eq_refl); exact R18 | rewrite E32; reflexivity | unfold SHADOW_OFF; lia | lia]. }
  { repeat (apply awr_ok_cons_ro; [cbn; lia|]).
    eapply awr_ok_cons_gen; [reflexivity | cbn [ew ewset Nat.eqb]; rewrite OLD2 by lia; exact U37 | |].
    { intros a Ha. cbn [YP09.r_wlo YP09.r_whi] in Ha. replace a with (res + c) by (unfold q in Ha; lia).
      eapply (awr_new_block_any SEGS B LAWS); [exact (ajournal_init SEGS B JOINED_STK FPj ly S W regs mem md ch HPRE) | exact (proj1 HJ2) | exact Eab
        | unfold jtot; pose proof (jw_need_nonneg ws); lia | exact Hres_in | unfold jtot in *; lia]. }
    apply awr_ok_nil. }
  lazymatch goal with Hfr : frame_of _ _ (mrestrict _ _) (mrestrict _ _) |- _ =>
  pose proof (kept_of_frame (segs := SEGS) _ _ _ _ _ (fun a => q <= a < q + 1) Hfr
    ltac:(intros b wlo whi a Hin Hrr; vm_compute in Hin;
      repeat (destruct Hin as [Hq | Hin]; [injection Hq as <- <- <-; cbn [base_val ew ewset Nat.eqb] in Hrr; rewrite ?OLD2 in Hrr by lia; rewrite ?U37, ?U35, ?U9, ?U18 in Hrr; lia|]); destruct Hin)) as UN3 end.
  lazymatch type of HS with st_ok _ _ _ (restrict _ ?mz) => rename mz into msz end.
  destruct (jw_tr (w_H Wc) (ms_mem ms2) (ms_mem msz) res (join_sp (firstn i ws))) as (HFR4 & HOP4 & HBY4);
    [ intros a Ha; apply UN3; [lia | unfold q; lia]
    | intros j Hj Ha; eapply apresent_grows; [eassumption | exact Ha]
    | intros a Ha; unfold q, c, jcur in *; apply UN3; lia | exact HFR3 | exact HOP3 | exact HBY3 |].
  pmkst HS.
  prreg HS (1%bv : bv 5) T1. prreg HS (2%bv : bv 5) T2. prreg HS (3%bv : bv 5) T3. prreg HS (4%bv : bv 5) T4.
  prreg HS (8%bv : bv 5) T8. prreg HS (9%bv : bv 5) T9. prreg HS (10%bv : bv 5) T10. prreg HS (11%bv : bv 5) T11.
  prreg HS (12%bv : bv 5) T12. prreg HS (18%bv : bv 5) T18. prreg HS (19%bv : bv 5) T19. prreg HS (20%bv : bv 5) T20.
  prreg HS (21%bv : bv 5) T21. prreg HS (23%bv : bv 5) T23. prreg HS (24%bv : bv 5) T24. prreg HS (25%bv : bv 5) T25.
  prreg HS (26%bv : bv 5) T26.
  rewrite ?OLD2 in T2, T3, T4, T9, T10, T11, T18, T19, T21, T23, T24, T25, T26 by lia.
  rewrite (EE 2%nat 2%bv eq_refl), R2 in T2.
  rewrite (EE 3%nat 3%bv eq_refl), R3 in T3.
  rewrite (EE 4%nat 4%bv eq_refl), R4 in T4.
  rewrite (EE 9%nat 9%bv eq_refl), R9 in T9.
  rewrite (EE 18%nat 18%bv eq_refl), R18 in T18.
  rewrite (EE 19%nat 19%bv eq_refl), R19 in T19.
  rewrite (EE 24%nat 24%bv eq_refl), R24 in T24.
  rewrite (EE 25%nat 25%bv eq_refl), R25 in T25.
  rewrite (EE 26%nat 26%bv eq_refl), R26 in T26.
  rewrite E32 in T21. change (Z_to_bv 64 jSB) with (w64 SHADOW_OFF) in T21.
  rewrite E36 in T11.
  rewrite E37 in T10. rewrite ?unsigned_lit_small in T10 by (unfold q; lia).
  rewrite (EE 23%nat 23%bv eq_refl), R23 in T23. unfold w64 in T23. rewrite ?unsigned_lit_small in T23 by lia.
  rewrite E44, HQ2 in T12, T20.
  assert (T22 : getr (ms_regs msz) 22 = w64 (SHADOW_OFF + (W0 + 24) / 8)).
  { jw_rawreg HS (22%bv : bv 5) Hr.
    rewrite Hr. rewrite (denot_shx _ 9 32 0 (W0 + 24) jSB); [unfold jSB; rewrite Z.add_0_r; reflexivity
    | cbn [ew ewset Nat.eqb]; rewrite ?OLD2 by lia; rewrite (EE 9%nat 9%bv eq_refl); exact R9
    | cbn [ew ewset Nat.eqb]; rewrite ?OLD2 by lia; exact E32 | lia | lia | lia | unfold jSB, SHADOW_OFF; lia]. }
  assert (T27 : getr (ms_regs msz) 27 = w64 (SHADOW_OFF + (W0 + 16) / 8)).
  { jw_rawreg HS (27%bv : bv 5) Hr27.
    rewrite Hr27. rewrite (denot_shx _ 18 32 0 (W0 + 16) jSB); [unfold jSB; rewrite Z.add_0_r; reflexivity
    | cbn [ew ewset Nat.eqb]; rewrite ?OLD2 by lia; rewrite (EE 18%nat 18%bv eq_refl); exact R18
    | cbn [ew ewset Nat.eqb]; rewrite ?OLD2 by lia; exact E32 | lia | lia | lia | unfold jSB, SHADOW_OFF; lia]. }
  apply (jw_C i lyc Sc Wc (ms_regs msz) (ms_mem msz) _ res Hi).
  + intros lyc' Sc' Wc' rB' mB' dB' Hlt HLB'. exact (IHk (Datatypes.S i) lyc' Sc' Wc' rB' mB' dB' res ltac:(lia) Hlt HLB').
  + exact HJ2. + exact Eab. + exact Hres. + exact MLE. + exact HFR4. + exact HOP4.
  + assert (Hjs : jsep i = []) by (rewrite Hi0; reflexivity). rewrite Hjs, app_nil_r. exact HBY4.
  + exact T1. + exact T2. + exact T3. + exact T4.
  + rewrite T8; reflexivity.
  + exact T9. + exact T18. + exact T19.
  + rewrite T20. reflexivity.
  + exact T21. + exact T22.
  + rewrite T10. replace (jsep i) with (@nil byte) by (rewrite Hi0; reflexivity). cbn [length]. unfold w64. f_equal. unfold q. lia.
  + exact T11.
  + rewrite T12. reflexivity.
  + rewrite T23. replace (jsep i) with (@nil byte) by (rewrite Hi0; reflexivity). cbn [length]. unfold w64. f_equal. lia.
  + exact T24. + exact T25. + exact T26. + exact T27.
- (* i <> 0: the separator at q *)
  rewrite branch_eq_U, U_SLit in Hc. rewrite (U_atom _ 24 (8 * Z.of_nat i)) in Hc;
    [| cbn [ew ewset Nat.eqb]; rewrite OLD2 by lia; rewrite (EE 24%nat 24%bv eq_refl); exact R24 | lia].
  change (zcanon 0) with 0 in Hc. apply Z.eqb_neq in Hc. assert (i <> 0%nat) as Hi0 by lia.
  paj_run_tok RUN HS HJ2 SHOK2 jBspan.
  { rewrite <- (aview_rd_of SEGS). destruct (jw_argv i _ _ _ _ _ _ Hi HJ2) as (_ & _ & _ & RAP2).
    rewrite (U_atom _ 32 SHADOW_OFF), (U_atom _ 35 p); [exact RAP2 | | | |]; cbn [ew ewset Nat.eqb]; rewrite ?OLD2 by lia;
    first [exact E35 | rewrite E32; reflexivity | unfold SHADOW_OFF; lia | lia]. }
  { rewrite <- (aview_rd_of SEGS). destruct (jw_struct _ _ _ _ _ _ HJ2) as (_ & _ & SRA2).
    rewrite (U_atom _ 32 SHADOW_OFF), (U_atom _ 18 (W0 + 16)); [apply (range_addressable_sub _ _ (W0 + 16) 16); [exact SRA2 | lia | lia] | | | |];
    cbn [ew ewset Nat.eqb]; rewrite ?OLD2 by lia; first [rewrite (EE 18%nat 18%bv eq_refl); exact R18 | rewrite E32; reflexivity | unfold SHADOW_OFF; lia | lia]. }
  { repeat (apply awr_ok_cons_ro; [cbn; lia|]).
    eapply awr_ok_cons_gen; [reflexivity | cbn [ew ewset Nat.eqb]; rewrite OLD2 by lia; exact U37 | |].
    { intros a Ha. cbn [YP09.r_wlo YP09.r_whi] in Ha. replace a with (res + c) by (unfold q in Ha; lia).
      eapply (awr_new_block_any SEGS B LAWS); [exact (ajournal_init SEGS B JOINED_STK FPj ly S W regs mem md ch HPRE) | exact (proj1 HJ2) | exact Eab
        | unfold jtot; pose proof (jw_need_nonneg ws); lia | exact Hres_in | unfold jtot in *; lia]. }
    apply awr_ok_nil. }
  lazymatch goal with Hfr : frame_of _ _ (mrestrict _ _) (mrestrict _ _) |- _ =>
  pose proof (kept_of_frame (segs := SEGS) _ _ _ _ _ (fun a => q <= a < q + 1) Hfr
    ltac:(intros b wlo whi a Hin Hrr; vm_compute in Hin;
      repeat (destruct Hin as [Hq | Hin]; [injection Hq as <- <- <-; cbn [base_val ew ewset Nat.eqb] in Hrr; rewrite ?OLD2 in Hrr by lia; rewrite ?U37, ?U35, ?U9, ?U18 in Hrr; lia|]); destruct Hin)) as UN3 end.
  lazymatch type of HS with st_ok _ _ _ (restrict _ ?mz) => rename mz into msz end.
  lazymatch type of HS with st_ok _ ?Ef ?ssx (restrict _ ?msx) =>
    let r3 := eval vm_compute in (nth 3 (ss_mem ssx) got_regionP) in
    pose proof (st_ok_region_nth Ef ssx (restrict _ msx) 3 r3 HS ltac:(vm_compute; reflexivity)) as RQ;
    cbn [ms_mem restrict] in RQ end.
  pose proof (field_of_region_any _ _ _ _ _ _ _ _ _ 0 1%N (SLit 32) RQ
    ltac:(cbn [ew ewset Nat.eqb]; rewrite OLD2 by lia; exact U37) ltac:(left; reflexivity) ltac:(cbn; lia)) as VQ.
  cbn [sv_denot] in VQ. rewrite unsigned_lit_small in VQ by lia. change (2 ^ (8 * Z.of_N 1)) with 256 in VQ.
  rewrite Z.mod_small in VQ by lia. rewrite Z.add_0_r in VQ. apply jw_aval_of_val in VQ.
  destruct (jw_tr (w_H Wc) (ms_mem ms2) (ms_mem msz) res (join_sp (firstn i ws))) as (HFR4 & HOP4 & HBY4);
    [ intros a Ha; apply UN3; [lia | unfold q; lia]
    | intros j Hj Ha; eapply apresent_grows; [eassumption | exact Ha]
    | intros a Ha; unfold q, c, jcur in *; apply UN3; lia | exact HFR3 | exact HOP3 | exact HBY3 |].
  pmkst HS.
  prreg HS (1%bv : bv 5) T1. prreg HS (2%bv : bv 5) T2. prreg HS (3%bv : bv 5) T3. prreg HS (4%bv : bv 5) T4.
  prreg HS (8%bv : bv 5) T8. prreg HS (9%bv : bv 5) T9. prreg HS (10%bv : bv 5) T10. prreg HS (11%bv : bv 5) T11.
  prreg HS (12%bv : bv 5) T12. prreg HS (18%bv : bv 5) T18. prreg HS (19%bv : bv 5) T19. prreg HS (20%bv : bv 5) T20.
  prreg HS (21%bv : bv 5) T21. prreg HS (23%bv : bv 5) T23. prreg HS (24%bv : bv 5) T24. prreg HS (25%bv : bv 5) T25.
  prreg HS (26%bv : bv 5) T26.
  rewrite ?OLD2 in T2, T3, T4, T9, T10, T11, T18, T19, T21, T23, T24, T25, T26 by lia.
  rewrite (EE 2%nat 2%bv eq_refl), R2 in T2.
  rewrite (EE 3%nat 3%bv eq_refl), R3 in T3.
  rewrite (EE 4%nat 4%bv eq_refl), R4 in T4.
  rewrite (EE 9%nat 9%bv eq_refl), R9 in T9.
  rewrite (EE 18%nat 18%bv eq_refl), R18 in T18.
  rewrite (EE 19%nat 19%bv eq_refl), R19 in T19.
  rewrite (EE 24%nat 24%bv eq_refl), R24 in T24.
  rewrite (EE 25%nat 25%bv eq_refl), R25 in T25.
  rewrite (EE 26%nat 26%bv eq_refl), R26 in T26.
  rewrite E32 in T21. change (Z_to_bv 64 jSB) with (w64 SHADOW_OFF) in T21.
  rewrite E36 in T11.
  rewrite E37 in T10. rewrite ?unsigned_lit_small in T10 by (unfold q; lia).
  rewrite (EE 23%nat 23%bv eq_refl), R23 in T23. unfold w64 in T23. rewrite ?unsigned_lit_small in T23 by lia.
  rewrite E44, HQ2 in T12, T20.
  assert (T22 : getr (ms_regs msz) 22 = w64 (SHADOW_OFF + (W0 + 24) / 8)).
  { jw_rawreg HS (22%bv : bv 5) Hr.
    rewrite Hr. rewrite (denot_shx _ 9 32 0 (W0 + 24) jSB); [unfold jSB; rewrite Z.add_0_r; reflexivity
    | cbn [ew ewset Nat.eqb]; rewrite ?OLD2 by lia; rewrite (EE 9%nat 9%bv eq_refl); exact R9
    | cbn [ew ewset Nat.eqb]; rewrite ?OLD2 by lia; exact E32 | lia | lia | lia | unfold jSB, SHADOW_OFF; lia]. }
  assert (T27 : getr (ms_regs msz) 27 = w64 (SHADOW_OFF + (W0 + 16) / 8)).
  { jw_rawreg HS (27%bv : bv 5) Hr27.
    rewrite Hr27. rewrite (denot_shx _ 18 32 0 (W0 + 16) jSB); [unfold jSB; rewrite Z.add_0_r; reflexivity
    | cbn [ew ewset Nat.eqb]; rewrite ?OLD2 by lia; rewrite (EE 18%nat 18%bv eq_refl); exact R18
    | cbn [ew ewset Nat.eqb]; rewrite ?OLD2 by lia; exact E32 | lia | lia | lia | unfold jSB, SHADOW_OFF; lia]. }
  apply (jw_C i lyc Sc Wc (ms_regs msz) (ms_mem msz) _ res Hi).
  + intros lyc' Sc' Wc' rB' mB' dB' Hlt HLB'. exact (IHk (Datatypes.S i) lyc' Sc' Wc' rB' mB' dB' res ltac:(lia) Hlt HLB').
  + exact HJ2. + exact Eab. + exact Hres. + exact MLE. + exact HFR4. + exact HOP4.
  + replace (jsep i) with [SPACE] by (unfold jsep; destruct (i =? 0)%nat eqn:Ei; [apply Nat.eqb_eq in Ei; lia | reflexivity]).
    intros j Hj. rewrite length_app in Hj. cbn [length] in Hj.
    destruct (Nat.lt_ge_cases j (length (join_sp (firstn i ws)))) as [Hlt | Hge].
    * rewrite app_nth1 by exact Hlt. exact (HBY4 j Hlt).
    * assert (j = length (join_sp (firstn i ws))) as -> by lia. rewrite app_nth2 by lia. rewrite Nat.sub_diag. cbn [nth].
      pose proof (VQ 0%nat ltac:(lia)) as V0. rewrite Z.add_0_r in V0. unfold q, c, jcur in V0. rewrite V0. reflexivity.
  + exact T1. + exact T2. + exact T3. + exact T4.
  + rewrite T8; reflexivity.
  + exact T9. + exact T18. + exact T19.
  + rewrite T20. reflexivity.
  + exact T21. + exact T22.
  + rewrite T10. replace (jsep i) with [SPACE] by (unfold jsep; destruct (i =? 0)%nat eqn:Ei; [apply Nat.eqb_eq in Ei; lia | reflexivity]). cbn [length]. unfold w64; f_equal; try (unfold q; lia).
  + exact T11.
  + rewrite T12. reflexivity.
  + rewrite T23. replace (jsep i) with [SPACE] by (unfold jsep; destruct (i =? 0)%nat eqn:Ei; [apply Nat.eqb_eq in Ei; lia | reflexivity]). cbn [length]. unfold w64; f_equal; try lia.
  + exact T24. + exact T25. + exact T26. + exact T27.
Qed.
(* after the malloc call (0x88c4c .. 0x88c98): the null check (not taken), the block's first byte zeroed, the
   partial-granule bound to 8(sp), then loop B (n > 0) or the terminator (n = 0) *)
Lemma jw_M2 : forall lyc Sc Wc rM mM dM res,
ajournal SEGS B JOINED_STK sp0 FPj ly S W mem md [] lyc Sc Wc mM dM 1 ->
ablocks B lyc Sc = ablocks B ly S ++ [(res, jtot)] -> 4096 <= res -> mo_le MT S Sc (XM_JOINED MT ws) ->
jframe (mrestrict (w_H Wc) mM) -> (forall j, 0 <= j < 8 -> apresent (w_H Wc) mM (outp + j)) ->
getr rM 2 = w64 (sp0 - 128) -> getr rM 3 = w64 (as_gp B) -> getr rM 4 = w64 (as_tp B) ->
getr rM 9 = w64 (W0 + 24) -> getr rM 10 = w64 res -> getr rM 18 = w64 (W0 + 16) -> getr rM 21 = w64 SHADOW_OFF ->
getr rM 22 = w64 (SHADOW_OFF + (W0 + 24) / 8) -> getr rM 27 = w64 ((W0 + 16) / 8) ->
SRr SEGS Wc (mkCfg (mkst rM (Z_to_bv 64 (BASE + 10012)) mM (seg_rom SEGS)) dM) JPOST.
Proof.
intros lyc Sc Wc rM mM dM res HJ Eab Hres MLE HFR HOP R2 R3 R4 R9 R10 R18 R21 R22 R27. jctx.
pose proof HJ as (HAR & Hly & _ & _ & _ & Hfrs & _ & _ & _ & _ & _ & _ & _ & Hpres & _).
destruct (jw_ly _ _ _ _ _ _ HJ) as (Elo & Ehi & Etop).
assert (Hres_in : In (res, jtot) (ablocks B lyc Sc)) by (rewrite Eab; apply in_or_app; right; left; reflexivity).
destruct (al_blocks _ _ LAWS _ _ _ _ _ res jtot HAR Hres_in) as (Hr16 & Hr4096 & Hrceil & Hrapp & Hrpres & _ & Hrm).
pose proof (req_size_pos jtot ltac:(unfold jtot; pose proof (jw_need_nonneg ws); lia)) as [Hq1 Hq2].
pose proof alloc_ceiling_value as [_ HAC2].
destruct (jw_struct _ _ _ _ _ _ HJ) as (SN & SA & SRA).
(* the seed: atoms 32 SB, 33 n *)
set (E := Eimg (Ereg rM [Z_to_bv 64 jSB; Z_to_bv 64 nW])).
assert (HEI : img_env VAL A_LIM E) by apply Eimg_env.
assert (EE : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E n = getr rM r)
  by (intros n r Hn; apply ew_Eimg_Ereg_nat; exact Hn).
assert (E32 : ew E 32 = Z_to_bv 64 jSB) by (unfold E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra rM _ 0)).
assert (E33 : ew E 33 = Z_to_bv 64 nW) by (unfold E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra rM _ 1)).
assert (U2 : bv_unsigned (ew E 2) = sp0 - 128) by (rewrite (EE 2%nat 2%bv eq_refl), R2; apply unsigned_lit_small; lia).
assert (U9 : bv_unsigned (ew E 9) = W0 + 24) by (rewrite (EE 9%nat 9%bv eq_refl), R9; apply unsigned_lit_small; lia).
assert (U10 : bv_unsigned (ew E 10) = res) by (rewrite (EE 10%nat 10%bv eq_refl), R10; apply unsigned_lit_small; lia).
assert (HS : st_ok_pi SEGS VAL E ssM2 (restrict (w_H Wc) (mkst rM (Z_to_bv 64 (BASE + 10012)) mM (seg_rom SEGS)))).
{ rewrite restrict_mkst_fx. unfold ssM2. apply pa_entry_st_ok_full.
  - change regsM2 with (sr_set (sr_set (sr_set sr_atoms 21 (SOff 32 0)) 22 (jshx 9)) 27 (jsrl 18 0)).
    apply regs_ok_rereg; [apply regs_ok_rereg; [apply regs_ok_rereg; [apply regs_ok_Eimg_Ereg | reflexivity |] | reflexivity |] | reflexivity |].
    + cbn [sv_denot]. rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned. exact R21.
    + unfold jshx. rewrite (denot_shx E 9 32 0 (W0 + 24) jSB) by (first [rewrite (EE 9%nat 9%bv eq_refl); exact R9 | exact E32 | unfold jSB, SHADOW_OFF; lia | lia]).
      rewrite R22. unfold jSB. rewrite Z.add_0_r. reflexivity.
    + unfold jsrl. rewrite (jw_srl3 E 18 0 (W0 + 16));
      [ rewrite Z.add_0_r; exact R27 | rewrite (EE 18%nat 18%bv eq_refl); exact R18 | lia | lia | lia].
  - vm_compute. reflexivity.
  - repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
      cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
    + rewrite U10. split; [lia|]. split; [lia|]. split; [|constructor].
      intros o Ho. apply (apresent_writable SEGS). apply (proj1 (Hrpres (res + o) ltac:(lia))).
    + rewrite U2. split; [lia|]. split; [lia|]. split; [|constructor].
      intros o Ho. apply (apresent_writable SEGS). apply Hpres. lia.
    + rewrite U9. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|]. apply Forall_cons; [|apply Forall_nil].
      apply (chunk_ok_val SEGS E _ (W0 + 24) 0 4 (SOff 33 0) nW);
      [ cbn [sv_denot]; rewrite E33, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | cbn; lia | cbn; lia |].
      rewrite Z.add_0_r. exact (jw_val_of_aval _ _ _ _ _ SN).
  - apply pairwise_disjoint_of_extents. unfold extent_of_region.
    cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite U10, U2, U9.
    cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd]. repeat split; lia.
  - split; [|split; exact I].
    cbn [f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
    rewrite U2, U9, U10, E32, E33. rewrite !unsigned_lit_small by (unfold jSB, SHADOW_OFF; lia).
    unfold jstklo, jstkhi8, jheaphi, jSB. change (2 ^ 4) with 16. rewrite Z.pow_0_r, !Z.mod_1_r.
    repeat split; try exact I; try lia.
    replace (sp0 - 128) with (sp0 + (-8) * 16) by lia. rewrite Z_mod_plus_full. exact Hal160. }
assert (UB : U E jBx = SHADOW_OFF) by (unfold jBx; apply U_atom; [rewrite E32; reflexivity | unfold SHADOW_OFF; lia]).
assert (SHOK : sh_ok SEGS jBx SHM2 E (mrestrict (w_H Wc) mM)).
{ unfold sh_ok, SHM2. apply Forall_cons; [|apply Forall_nil].
  unfold shent_ok, app_apart. cbn [she_m she_lo she_hi].
  assert (U10' : U E (SOff 10 0) = res) by (apply U_atom; [rewrite (EE 10%nat 10%bv eq_refl); exact R10 | lia]).
  rewrite UB, U10', <- (aview_rd_of SEGS). split.
  - apply (range_addressable_of_block SEGS B LAWS lyc Sc Wc mM dM res jtot); [exact HAR | exact Hres_in | lia | lia].
  - intros a Ha. destruct Hrapp as [_ [Hlow | [Hhi1 Hhi2]]]; unfold kLowShadowBeg, kHighMemBeg, SHADOW_OFF in *; lia. }
paj_run_tok RUN HS HJ SHOK jBspan.
{ rewrite <- (aview_rd_of SEGS). rewrite UB, (U_atom E 9 (W0 + 24)) by (first [rewrite (EE 9%nat 9%bv eq_refl); exact R9 | lia]).
  apply (range_addressable_sub _ _ (W0 + 16) 16); [exact SRA | lia | lia]. }
{ unfold ssM2. cbn [ss_mem].
  eapply awr_ok_cons_gen; [reflexivity | exact U10 | |].
  { intros a Ha. cbn [YP09.r_wlo YP09.r_whi] in Ha. replace a with (res + (a - res)) by lia.
    eapply (awr_new_block_any SEGS B LAWS); [exact (ajournal_init SEGS B JOINED_STK FPj ly S W regs mem md ch HPRE) | exact HAR | exact Eab
      | unfold jtot; pose proof (jw_need_nonneg ws); lia | exact Hres_in | lia]. }
  eapply awr_ok_cons_stack_off; [reflexivity | exact U2 | cbn; rewrite HJS; lia | cbn; lia |].
  apply awr_ok_cons_ro; [cbn; lia|]. apply awr_ok_nil. }
lazymatch goal with Hfr : frame_of E _ (mrestrict _ _) (mrestrict _ _) |- _ =>
pose proof (kept_of_frame (segs := SEGS) _ _ _ _ _ (fun a => (res <= a < res + 1) \/ (sp0 - 120 <= a < sp0 - 112)) Hfr
  ltac:(intros b wlo whi a Hin Hrr; vm_compute in Hin;
    repeat (destruct Hin as [Hq | Hin]; [injection Hq as <- <- <-; cbn [base_val] in Hrr; rewrite ?U10, ?U2, ?U9 in Hrr; lia|]); destruct Hin)) as UN1; clear Hfr end.
lazymatch type of HS with st_ok_pi _ _ _ _ (restrict _ ?mz) => rename mz into ms1 end.
assert (HFR1 : jframe (mrestrict (w_H Wc) (ms_mem ms1))).
{ apply (jw_frame_kept _ _ _ _ HFR). intros a Ha. apply UN1; [lia | lia]. }
assert (HOP1 : forall j, 0 <= j < 8 -> apresent (w_H Wc) (ms_mem ms1) (outp + j)).
{ intros j Hj. eapply apresent_grows; [eassumption | exact (HOP j Hj)]. }
psrr_branch_tok RUN BR HS SHOK jBspan.
- (* n = 0: the terminator *)
  rewrite (jw_branch_ge _ _ _ 0 nW) in Hc; [| reflexivity | cbn [sv_denot ew ewset Nat.eqb]; rewrite E33, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | lia | lia].
  apply Z.leb_le in Hc. assert (Hws : ws = []) by (destruct ws as [|wz ws']; [reflexivity | cbn [length] in Hc; lia]).
  paj_run_to_tok RUNTO HS HJ SHOK jBspan PC_F.
  { cbn [ss_mem].
    eapply awr_ok_cons_gen; [reflexivity | cbn [ew ewset Nat.eqb]; exact U10 | |].
    { intros a Ha. cbn [YP09.r_wlo YP09.r_whi] in Ha. replace a with (res + (a - res)) by lia.
      eapply (awr_new_block_any SEGS B LAWS); [exact (ajournal_init SEGS B JOINED_STK FPj ly S W regs mem md ch HPRE) | exact HAR | exact Eab
        | unfold jtot; pose proof (jw_need_nonneg ws); lia | exact Hres_in | lia]. }
    eapply awr_ok_cons_stack_off; [reflexivity | cbn [ew ewset Nat.eqb]; exact U2 | cbn; rewrite HJS; lia | cbn; lia |].
    apply awr_ok_cons_ro; [cbn; lia|]. apply awr_ok_nil. }
  lazymatch goal with Hfr : frame_of _ _ (mrestrict _ _) (mrestrict _ _) |- _ =>
  pose proof (kept_of_frame (segs := SEGS) _ _ _ _ _ (fun a => (res <= a < res + 1) \/ (sp0 - 120 <= a < sp0 - 112)) Hfr
    ltac:(intros b wlo whi a Hin Hrr; vm_compute in Hin;
      repeat (destruct Hin as [Hq | Hin]; [injection Hq as <- <- <-; cbn [base_val ew ewset Nat.eqb] in Hrr; rewrite ?U10, ?U2, ?U9 in Hrr; lia|]); destruct Hin)) as UN2 end.
  pmkst HS.
  prreg HS (2%bv : bv 5) T2. prreg HS (3%bv : bv 5) T3. prreg HS (4%bv : bv 5) T4. prreg HS (10%bv : bv 5) T10.
  prreg HS (19%bv : bv 5) T19. prreg HS (21%bv : bv 5) T21. prreg HS (23%bv : bv 5) T23.
  apply (jw_final lyc Sc Wc (ms_regs ms) (ms_mem ms) _ res HJ Eab Hres MLE).
  + apply (jw_frame_kept _ _ _ _ HFR1). intros a Ha. apply UN2; lia.
  + intros j Hj. eapply apresent_grows; [eassumption | exact (HOP1 j Hj)].
  + rewrite Hws. intros j Hj. cbn in Hj. lia.
  + rewrite T2, (EE 2%nat 2%bv eq_refl). exact R2.
  + rewrite T3, (EE 3%nat 3%bv eq_refl). exact R3.
  + rewrite T4, (EE 4%nat 4%bv eq_refl). exact R4.
  + rewrite Hws. cbn [join_sp length]. rewrite T10, (EE 10%nat 10%bv eq_refl), R10.
    unfold w64. f_equal. lia.
  + rewrite T19, (EE 10%nat 10%bv eq_refl). exact R10.
  + rewrite T21, E32. reflexivity.
  + rewrite T23, Hws. reflexivity.
- (* n > 0: loop B from word 0 *)
  rewrite (jw_branch_ge _ _ _ 0 nW) in Hc; [| reflexivity | cbn [sv_denot ew ewset Nat.eqb]; rewrite E33, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | lia | lia].
  apply Z.leb_gt in Hc.
  paj_run_to_tok RUNTO HS HJ SHOK jBspan PC_B.
  { cbn [ss_mem].
    eapply awr_ok_cons_gen; [reflexivity | cbn [ew ewset Nat.eqb]; exact U10 | |].
    { intros a Ha. cbn [YP09.r_wlo YP09.r_whi] in Ha. replace a with (res + (a - res)) by lia.
      eapply (awr_new_block_any SEGS B LAWS); [exact (ajournal_init SEGS B JOINED_STK FPj ly S W regs mem md ch HPRE) | exact HAR | exact Eab
        | unfold jtot; pose proof (jw_need_nonneg ws); lia | exact Hres_in | lia]. }
    eapply awr_ok_cons_stack_off; [reflexivity | cbn [ew ewset Nat.eqb]; exact U2 | cbn; rewrite HJS; lia | cbn; lia |].
    apply awr_ok_cons_ro; [cbn; lia|]. apply awr_ok_nil. }
  lazymatch goal with Hfr : frame_of _ _ (mrestrict _ _) (mrestrict _ _) |- _ =>
  pose proof (kept_of_frame (segs := SEGS) _ _ _ _ _ (fun a => (res <= a < res + 1) \/ (sp0 - 120 <= a < sp0 - 112)) Hfr
    ltac:(intros b wlo whi a Hin Hrr; vm_compute in Hin;
      repeat (destruct Hin as [Hq | Hin]; [injection Hq as <- <- <-; cbn [base_val ew ewset Nat.eqb] in Hrr; rewrite ?U10, ?U2, ?U9 in Hrr; lia|]); destruct Hin)) as UN2 end.
  pmkst HS.
  prreg HS (2%bv : bv 5) T2. prreg HS (3%bv : bv 5) T3. prreg HS (4%bv : bv 5) T4. prreg HS (8%bv : bv 5) T8.
  prreg HS (9%bv : bv 5) T9. prreg HS (18%bv : bv 5) T18. prreg HS (19%bv : bv 5) T19. prreg HS (21%bv : bv 5) T21.
  prreg HS (23%bv : bv 5) T23. prreg HS (24%bv : bv 5) T24. prreg HS (25%bv : bv 5) T25.
  assert (T22 : getr (ms_regs ms) 22 = w64 (SHADOW_OFF + (W0 + 24) / 8)).
  { jw_rawreg HS (22%bv : bv 5) Hr.
    rewrite Hr. rewrite (denot_shx _ 9 32 0 (W0 + 24) jSB); [unfold jSB; rewrite Z.add_0_r; reflexivity
    | cbn [ew ewset Nat.eqb]; rewrite (EE 9%nat 9%bv eq_refl); exact R9 | cbn [ew ewset Nat.eqb]; exact E32 | lia | lia | lia | unfold jSB, SHADOW_OFF; lia]. }
  assert (T27 : getr (ms_regs ms) 27 = w64 (SHADOW_OFF + (W0 + 16) / 8)).
  { jw_rawreg HS (27%bv : bv 5) Hr27.
    rewrite Hr27. rewrite (denot_shx _ 18 32 0 (W0 + 16) jSB); [unfold jSB; rewrite Z.add_0_r; reflexivity
    | cbn [ew ewset Nat.eqb]; rewrite (EE 18%nat 18%bv eq_refl); exact R18 | cbn [ew ewset Nat.eqb]; exact E32 | lia | lia | lia | unfold jSB, SHADOW_OFF; lia]. }
  assert (T26 : getr (ms_regs ms) 26 = w64 (2 ^ 64 - 1 - res)).
  { jw_rawreg HS (26%bv : bv 5) Hr26.
    rewrite Hr26. apply (jw_den_not _ 10 res);
    [ cbn [ew ewset Nat.eqb]; rewrite (EE 10%nat 10%bv eq_refl); exact R10 | lia | reflexivity]. }
  apply (jw_loopB (length ws) 0 lyc Sc Wc (ms_regs ms) (ms_mem ms) _ res ltac:(lia) ltac:(lia)).
  split; [exact HJ|]. split; [exact Eab|]. split; [exact Hres|]. split; [exact MLE|].
  split; [apply (jw_frame_kept _ _ _ _ HFR1); intros a Ha; apply UN2; lia|].
  split; [intros j Hj; eapply apresent_grows; [eassumption | exact (HOP1 j Hj)]|].
  split.
  { intros j Hj. change (firstn 0 ws) with (@nil (list byte)) in Hj. cbn in Hj. lia. }
  split; [rewrite T2, (EE 2%nat 2%bv eq_refl); exact R2|].
  split; [rewrite T3, (EE 3%nat 3%bv eq_refl); exact R3|].
  split; [rewrite T4, (EE 4%nat 4%bv eq_refl); exact R4|].
  split; [rewrite T8; reflexivity|].
  split; [rewrite T9, (EE 9%nat 9%bv eq_refl); exact R9|].
  split; [rewrite T18, (EE 18%nat 18%bv eq_refl); exact R18|].
  split; [rewrite T19, (EE 10%nat 10%bv eq_refl); exact R10|].
  split; [rewrite T21, E32; reflexivity|].
  split; [exact T22|].
  split; [rewrite T23; reflexivity|].
  split; [rewrite T24; reflexivity|].
  split; [rewrite T25; reflexivity|].
  split; [exact T26 | exact T27].
Qed.
(* the malloc call (0x88c48) of join_need ws + 1 bytes, then jw_M2. s0 at the call holds the running length (n > 0,
   below alloc_ceiling: achain_low) or still the caller's value (n = 0: afn_pre's own chain); the caller of this
   lemma hands the matching achain, and achain_chain_pre (YCbq.v:327) turns it into the chain_pre the malloc rule
   reads, at the call's sp (a Theorem Labs lane's PASS4-REFIT.md section B) *)
Lemma jw_call : forall rT mT dT (s0v : Z) (chv : list (Z * Z * Z)),
ajournal SEGS B JOINED_STK sp0 FPj ly S W mem md [] ly S W mT dT 0 ->
jframe (mrestrict (w_H W) mT) -> (forall a, sp0 <= a < 2 ^ 64 -> rdW W mT a = rdW W mem a) ->
getr rT 1 = w64 (BASE + 10012) -> getr rT 2 = w64 (sp0 - 128) -> getr rT 3 = w64 (as_gp B) -> getr rT 4 = w64 (as_tp B) ->
getr rT 8 = w64 s0v -> 0 <= s0v < 2 ^ 64 -> achain ly (rdW W mem) sp0 s0v chv ->
getr rT 9 = w64 (W0 + 24) -> getr rT 10 = w64 jtot -> getr rT 18 = w64 (W0 + 16) ->
getr rT 21 = w64 SHADOW_OFF -> getr rT 22 = w64 (SHADOW_OFF + (W0 + 24) / 8) -> getr rT 27 = w64 ((W0 + 16) / 8) ->
SRr SEGS W (mkCfg (mkst rT (Z_to_bv 64 (SIG CS___interceptor_trampoline_malloc)) mT (seg_rom SEGS)) dT) JPOST.
Proof.
intros rT mT dT s0v chv HJ HFR KA R1 R2 R3 R4 R8 Hs0r HCW R9 R10 R18 R21 R22 R27. jctx.
pose proof (@pa_B_ok _ _ PI) as HBASE. pose proof (pa_base_lo (L := cmd_listing)) as HBLO.
rewrite (pal_malloc B TL).
assert (HspT : spZ rT = sp0 + -128) by (unfold spZ at 1; rewrite R2; unfold w64; rewrite unsigned_lit_small by lia; lia).
assert (Hjt : 0 < jtot < MALLOC_MAX) by (unfold jtot; pose proof (jw_need_nonneg ws); lia).
pose proof alloc_ceiling_value as [HAC1 HAC2].
assert (HCP : chain_pre ly (rdW W mT) rT chv).
{ apply (achain_chain_pre ly _ sp0 s0v chv rT).
  - exact (achain_kept ly (rdW W mem) (rdW W mT) sp0 s0v chv sp0 HCW ltac:(lia) ltac:(lia) KA).
  - rewrite HspT. rewrite HJS in Hslo0. lia.
  - unfold s0Z. rewrite R8. unfold w64. rewrite unsigned_lit_small by lia. reflexivity.
  - unfold raZ. rewrite R1. unfold w64. rewrite unsigned_lit_small by lia. lia. }
eapply SRr_bind.
{ eapply (amalloc04_sub SEGS B LAWS pa_segs_low MT (AMALLOC4 fx) W rT mT JOINED_STK sp0 FPj ly S W mem md [] ly S dT 0 jtot (-128)
    (Z_to_bv 64 (BASE + 10012)) chv HJ).
  - exact R10.
  - lia.
  - unfold LIVE_JOINED in HLIVE. lia.
  - exact HspT.
  - reflexivity.
  - lia.
  - rewrite Has, HJS. lia.
  - exact R3.
  - exact R4.
  - exact R1.
  - apply ret_ok_codeptr_v; [lia | reflexivity].
  - unfold EV_JOINED in HEV. lia.
  - exact HCP.
  - unfold XM_JOINED in MOK. exact MOK. }
cbv beta. intros W3 c3 Hwle3 (ly3 & S3 & regs2 & mem2 & md2 & res & -> & HJ3 & HP3 & Ha03 & Hfrs3 & Hres4096 & Eab3 & HK3 & MLE3 & HJt3).
replace (0 + 1) with 1 in HJ3 by reflexivity.
destruct HK3 as (K1 & _).
assert (Q2 : getr regs2 2 = w64 (sp0 - 128)) by (replace (2%bv : bv 5) with (Z_to_bv 5 2) by (apply bv_eq; reflexivity); rewrite (HP3 2 ltac:(unfold acallee_saved; lia)); replace (Z_to_bv 5 2) with (2%bv : bv 5) by (apply bv_eq; reflexivity); exact R2).
assert (Q3 : getr regs2 3 = w64 (as_gp B)) by (replace (3%bv : bv 5) with (Z_to_bv 5 3) by (apply bv_eq; reflexivity); rewrite (HP3 3 ltac:(unfold acallee_saved; lia)); replace (Z_to_bv 5 3) with (3%bv : bv 5) by (apply bv_eq; reflexivity); exact R3).
assert (Q4 : getr regs2 4 = w64 (as_tp B)) by (replace (4%bv : bv 5) with (Z_to_bv 5 4) by (apply bv_eq; reflexivity); rewrite (HP3 4 ltac:(unfold acallee_saved; lia)); replace (Z_to_bv 5 4) with (4%bv : bv 5) by (apply bv_eq; reflexivity); exact R4).
assert (Q9 : getr regs2 9 = w64 (W0 + 24)) by (replace (9%bv : bv 5) with (Z_to_bv 5 9) by (apply bv_eq; reflexivity); rewrite (HP3 9 ltac:(unfold acallee_saved; lia)); replace (Z_to_bv 5 9) with (9%bv : bv 5) by (apply bv_eq; reflexivity); exact R9).
assert (Q18 : getr regs2 18 = w64 (W0 + 16)) by (replace (18%bv : bv 5) with (Z_to_bv 5 18) by (apply bv_eq; reflexivity); rewrite (HP3 18 ltac:(unfold acallee_saved; lia)); replace (Z_to_bv 5 18) with (18%bv : bv 5) by (apply bv_eq; reflexivity); exact R18).
assert (Q21 : getr regs2 21 = w64 SHADOW_OFF) by (replace (21%bv : bv 5) with (Z_to_bv 5 21) by (apply bv_eq; reflexivity); rewrite (HP3 21 ltac:(unfold acallee_saved; lia)); replace (Z_to_bv 5 21) with (21%bv : bv 5) by (apply bv_eq; reflexivity); exact R21).
assert (Q22 : getr regs2 22 = w64 (SHADOW_OFF + (W0 + 24) / 8)) by (replace (22%bv : bv 5) with (Z_to_bv 5 22) by (apply bv_eq; reflexivity); rewrite (HP3 22 ltac:(unfold acallee_saved; lia)); replace (Z_to_bv 5 22) with (22%bv : bv 5) by (apply bv_eq; reflexivity); exact R22).
assert (Q27 : getr regs2 27 = w64 ((W0 + 16) / 8)) by (replace (27%bv : bv 5) with (Z_to_bv 5 27) by (apply bv_eq; reflexivity); rewrite (HP3 27 ltac:(unfold acallee_saved; lia)); replace (Z_to_bv 5 27) with (27%bv : bv 5) by (apply bv_eq; reflexivity); exact R27).
apply (jw_M2 ly3 S3 W3 regs2 mem2 md2 res HJ3 Eab3 Hres4096).
- unfold XM_JOINED. exact MLE3.
- apply (jw_frame_kept _ _ _ _ HFR). intros a Ha. apply K1; lia.
- intros j Hj. apply (apresent_of_aview SEGS); [lia | |].
  + intros Hi. pose proof (pa_segs_low _ Hi) as Hlo. unfold kLowMemEnd in Hlo. lia.
  + rewrite K1 by lia. rewrite KA by lia. apply aview_some_of_apresent. exact (HOPR j Hj).
- exact Q2. - exact Q3. - exact Q4. - exact Q9. - exact Ha03. - exact Q18. - exact Q21. - exact Q22. - exact Q27.
Qed.
(* the state at the head of loop A (0x88bf0) before word i: the walk has not called malloc yet, so the layout, the
   allocator state and the world are the entry's. s0 is the running length, s3 and s9 both hold w->w + 8i, s4 holds
   w->w, s7 the down-counter, s8 the flag `w->w <> 0` (a literal 1 here) and s11 the shadow index of &w->w *)
Definition LA (i : nat) (rA : bvmap 5 word) (mA : word -> option byte) (dA : Model) : Prop :=
ajournal SEGS B JOINED_STK sp0 FPj ly S W mem md [] ly S W mA dA 0 /\
jframe (mrestrict (w_H W) mA) /\ (forall a, sp0 <= a < 2 ^ 64 -> rdW W mA a = rdW W mem a) /\
getr rA 2 = w64 (sp0 - 128) /\ getr rA 3 = w64 (as_gp B) /\ getr rA 4 = w64 (as_tp B) /\
getr rA 8 = w64 (PJoin.join_need (firstn i ws)) /\
getr rA 9 = w64 (W0 + 24) /\ getr rA 18 = w64 (W0 + 16) /\
getr rA 19 = w64 (arr + 8 * Z.of_nat i) /\ getr rA 20 = w64 arr /\
getr rA 21 = w64 SHADOW_OFF /\ getr rA 22 = w64 (SHADOW_OFF + (W0 + 24) / 8) /\
getr rA 23 = w64 (nW - Z.of_nat i) /\ getr rA 24 = w64 1 /\
getr rA 25 = w64 (arr + 8 * Z.of_nat i) /\ getr rA 27 = w64 ((W0 + 16) / 8).
(* loop A (0x88bf0 .. 0x88c38): the four UBSan checks of w->w + 8i (0x88bf0, 0x88bfc, 0x88c00, 0x88c08, all decided
   by the seed's facts), the strlen entry on word i, the sum, then the next word or the malloc call *)
Lemma jw_loopA : forall (k i : nat) rA mA dA,
(length ws - i <= k)%nat -> (i < length ws)%nat -> LA i rA mA dA ->
SRr SEGS W (mkCfg (mkst rA (Z_to_bv 64 (BASE + PC_A)) mA (seg_rom SEGS)) dA) JPOST.
Proof.
induction k as [|k IHk]; intros i rA mA dA Hk Hi HLA; [lia|].
destruct HLA as (HJ & HFR & KA & R2 & R3 & R4 & R8 & R9 & R18 & R19 & R20 & R21 & R22 & R23 & R24 & R25 & R27).
jctx.
pose proof (@pa_B_ok _ _ PI) as HBASE. pose proof (pa_base_lo (L := cmd_listing)) as HBLO.
pose proof (jw_need_S ws i Hi) as ENS.
pose proof (jw_need_firstn ws (Datatypes.S i)) as HNF.
pose proof (jw_need_nonneg (firstn i ws)) as HN0.
pose proof HNEED as HMX. unfold MALLOC_MAX in HMX.
set (len := Z.of_nat (length (nth i ws []))) in *.
set (ni := PJoin.join_need (firstn i ws)) in *.
destruct (jw_argv i _ _ _ _ _ _ Hi HJ) as (Hp1 & Hp2 & VP & RAP).
destruct (jw_word i _ _ _ _ _ _ Hi HJ) as (Hw1 & Hw2 & HLM & Hstr & HRD & HTV & Hzone).
set (p := arr + 8 * Z.of_nat i) in *. set (wpi := nth i wp 0) in *.
pose proof alloc_ceiling_value as [HAC1 HAC2].
assert (Hp8 : p mod 8 = 0).
{ unfold p. replace (arr + 8 * Z.of_nat i) with (arr + Z.of_nat i * 8) by lia. rewrite Z_mod_plus_full. exact HARR8. }
(* the seed: atoms 32 SB, 33 the word's pointer *)
set (E := Eimg (Ereg rA [Z_to_bv 64 jSB; Z_to_bv 64 wpi])).
assert (HEI : img_env VAL A_LIM E) by apply Eimg_env.
assert (EE : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E n = getr rA r)
  by (intros n r Hn; apply ew_Eimg_Ereg_nat; exact Hn).
assert (E32 : ew E 32 = Z_to_bv 64 jSB) by (unfold E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra rA _ 0)).
assert (E33 : ew E 33 = Z_to_bv 64 wpi) by (unfold E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra rA _ 1)).
assert (U19 : bv_unsigned (ew E 19) = p) by (rewrite (EE 19%nat 19%bv eq_refl), R19; apply unsigned_lit_small; lia).
assert (Harr : 4096 <= arr) by (destruct HAB as (b & m & Hbm & Hb1 & _); destruct (al_blocks _ _ LAWS _ _ _ _ _ b m HAR0 Hbm) as (_ & Hb4 & _); lia).
assert (U20 : bv_unsigned (ew E 20) = arr) by (rewrite (EE 20%nat 20%bv eq_refl), R20; apply unsigned_lit_small; lia).
assert (HS : st_ok_pi SEGS VAL E ssA (restrict (w_H W) (mkst rA (Z_to_bv 64 (BASE + PC_A)) mA (seg_rom SEGS)))).
{ rewrite restrict_mkst_fx. unfold ssA. apply pa_entry_st_ok_full.
  - change regsA with (sr_set (sr_set (sr_set (sr_set (sr_set sr_atoms 21 (SOff 32 0)) 22 (jshx 9)) 24 (SLit 1)) 25 (SOff 19 0)) 27 (jsrl 18 0)).
    apply regs_ok_rereg;
      [apply regs_ok_rereg; [apply regs_ok_rereg; [apply regs_ok_rereg; [apply regs_ok_rereg;
        [apply regs_ok_Eimg_Ereg | reflexivity |] | reflexivity |] | reflexivity |] | reflexivity |] | reflexivity |].
    + cbn [sv_denot]. rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned. exact R21.
    + unfold jshx. rewrite (denot_shx E 9 32 0 (W0 + 24) jSB) by (first [rewrite (EE 9%nat 9%bv eq_refl); exact R9 | exact E32 | unfold jSB, SHADOW_OFF; lia | lia]).
      rewrite R22. unfold jSB. rewrite Z.add_0_r. reflexivity.
    + cbn [sv_denot]. exact R24.
    + cbn [sv_denot]. rewrite (EE 19%nat 19%bv eq_refl), R19, Z.add_0_r, Z_to_bv_bv_unsigned. exact R25.
    + unfold jsrl. rewrite (jw_srl3 E 18 0 (W0 + 16));
      [ rewrite Z.add_0_r; exact R27 | rewrite (EE 18%nat 18%bv eq_refl); exact R18 | lia | lia | lia].
  - vm_compute. reflexivity.
  - apply Forall_cons; [|apply Forall_nil]. unfold region_ok.
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val]. rewrite U19.
    split; [lia|]. split; [lia|]. split; [intros o Ho; lia|]. apply Forall_cons; [|apply Forall_nil].
    apply (chunk_ok_val SEGS E _ p 0 8 (SOff 33 0) wpi);
    [ cbn [sv_denot]; rewrite E33, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | cbn; lia | cbn; lia |].
    rewrite Z.add_0_r. exact (jw_val_of_aval _ _ _ _ _ VP).
  - apply pairwise_disjoint_of_extents. cbn. tauto.
  - split; [|split; [|exact I]].
    + cbn [f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
      rewrite U19, U20, E32. rewrite !unsigned_lit_small by (unfold jSB, SHADOW_OFF; lia).
      unfold jheaphi, jSB. change (2 ^ 3) with 8. rewrite Z.pow_0_r, !Z.mod_1_r.
      repeat split; first [exact I | exact Hp8 | lia].
    + cbn [f_conds conds_ok]. split; [|exact I].
      unfold acond_ok. cbn [ac_c ac_a ac_b].
      rewrite (jw_branch_geu E (SOff 19 0) (SOff 20 0) p arr);
        [ apply Z.leb_le; unfold p; lia
        | cbn [sv_denot]; rewrite (EE 19%nat 19%bv eq_refl), R19, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
        | cbn [sv_denot]; rewrite (EE 20%nat 20%bv eq_refl), R20, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
        | lia | lia]. }
assert (UB : U E jBx = SHADOW_OFF) by (unfold jBx; apply U_atom; [rewrite E32; reflexivity | unfold SHADOW_OFF; lia]).
assert (SHOK : sh_ok SEGS jBx [] E (mrestrict (w_H W) mA)) by apply Forall_nil.
paj_run_tok RUN HS HJ SHOK jBspan.
{ rewrite <- (aview_rd_of SEGS). rewrite UB, (U_atom E 19 p) by (first [rewrite (EE 19%nat 19%bv eq_refl); exact R19 | lia]). exact RAP. }
{ unfold ssA. cbn [ss_mem]. apply awr_ok_cons_ro; [cbn; lia|]. apply awr_ok_nil. }
lazymatch goal with Hfr : frame_of _ _ (mrestrict _ _) (mrestrict _ _) |- _ =>
pose proof (kept_of_frame (segs := SEGS) _ _ _ _ _ (fun _ => False) Hfr
  ltac:(intros b wlo whi a Hin Hrr; vm_compute in Hin;
    repeat (destruct Hin as [Hq | Hin]; [injection Hq as <- <- <-; cbn [base_val] in Hrr; lia|]); destruct Hin)) as UN1; clear Hfr end.
pmkst HS.
prreg HS (1%bv : bv 5) P1. prreg HS (2%bv : bv 5) P2. prreg HS (3%bv : bv 5) P3. prreg HS (4%bv : bv 5) P4. prreg HS (10%bv : bv 5) P10.
assert (HspT : spZ (ms_regs ms) = sp0 + -128).
{ unfold spZ at 1. rewrite P2, (EE 2%nat 2%bv eq_refl), R2. unfold w64. rewrite unsigned_lit_small by lia. lia. }
assert (P3' : getr (ms_regs ms) 3 = w64 (as_gp B)) by (rewrite P3, (EE 3%nat 3%bv eq_refl); exact R3).
assert (P4' : getr (ms_regs ms) 4 = w64 (as_tp B)) by (rewrite P4, (EE 4%nat 4%bv eq_refl); exact R4).
assert (P10' : getr (ms_regs ms) 10 = w64 wpi) by (rewrite P10, E33; reflexivity).
assert (HraT : YK0s.ret_ok (getr (ms_regs ms) 1)) by (rewrite P1; apply ret_ok_codeptr_v; [lia | reflexivity]).
destruct (jw_word i _ _ _ _ _ _ Hi HJ) as (_ & _ & _ & Hstr1 & HRD1 & HTV1 & _).
eapply SRr_bind.
{ eapply (jw_art_at ESTACK (fun _ => False) (SIG CS___interceptor_trampoline_strlen)
    W (ms_regs ms) (ms_mem ms) JOINED_STK sp0 FPj ly S W mem md [] ly S _ 0 (-128) (Z_to_bv 64 (BASE + 9972)) _ HJ HspT eq_refl
    ltac:(lia) ltac:(lia) ltac:(rewrite Hes, HJS; lia) P1 (fun a (H : False) => False_ind _ H)).
  apply (ASTRLEN fx ly S W (ms_regs ms) (ms_mem ms) _ wpi (nth i ws [])).
  - exact (ecall_pre_stk_at SEGS B ESTACK JOINED_STK sp0 FPj ly S W mem md [] ly S W (ms_mem ms) _ 0 (ms_regs ms) (-128) HJ HspT eq_refl
      ltac:(lia) ltac:(lia) ltac:(rewrite Hes, HJS; lia) HraT P3' P4').
  - exact P10'.
  - lia.
  - apply (astr_atR_view SEGS). exact Hstr1.
  - apply HRD1. rewrite HspT, Hes. lia.
  - exact HTV1.
  - exact (jw_rom _ _ _ _ _ _ HJ). }
cbv beta. intros W2 c2 _ (-> & regs2 & mem2 & md2 & -> & HJ2 & HP2 & HQ2 & HK2 & HPR2).
jafter_call_keep_pi HS 40%nat regs2 (mrestrict (w_H W) mem2) HP2 [0]%nat HS2.
match type of HS2 with ?t -> _ => assert (HRK : t); [|specialize (HS2 HRK); clear HRK] end.
{ cbn [ms_mem restrict]. apply Forall_cons; [|apply Forall_nil].
  eapply jw_rkept; [cbn [ew ewset Nat.eqb]; exact U19 | intros a Ha; apply HK2; [lia | rewrite Hes; lia | tauto] | intros a Ha; lia]. }
assert (KA2 : forall a, sp0 - 112 <= a < 2 ^ 64 -> rdW W mem2 a = rdW W mA a).
{ intros a Ha. rewrite HK2 by (first [lia | rewrite Hes; lia | tauto]). apply UN1; [lia | tauto]. }
clear HS. rewrite <- restrict_mkst_fx in HS2. rename HS2 into HS.
lazymatch type of HS with st_ok_pi _ _ ?E2t _ _ => remember E2t as E2 eqn:HE2 end.
assert (HEI2 : img_env VAL A_LIM E2) by (rewrite HE2; apply img_env_havoc; [assumption | cbv; lia]).
assert (OLD2 : forall n, (n < 40)%nat -> ew E2 n = ew E n).
{ intros n Hn. rewrite HE2, YN3v.ew_havoc_old by lia. repeat rewrite ew_ewset_other by lia. reflexivity. }
assert (E44 : ew E2 44 = getr regs2 10) by (rewrite HE2; reflexivity).
clear HE2.
assert (SHOK2 : sh_ok SEGS jBx [] E2 (mrestrict (w_H W) mem2)) by apply Forall_nil.
paj_run_tok RUN HS HJ2 SHOK2 jBspan.
{ apply awr_ok_cons_ro; [cbn; lia|]. apply awr_ok_nil. }
lazymatch goal with Hfr : frame_of _ _ (mrestrict _ _) (mrestrict _ _) |- _ =>
pose proof (kept_of_frame (segs := SEGS) _ _ _ _ _ (fun _ => False) Hfr
  ltac:(intros b wlo whi a Hin Hrr; vm_compute in Hin;
    repeat (destruct Hin as [Hq | Hin]; [injection Hq as <- <- <-; cbn [base_val ew ewset Nat.eqb] in Hrr; lia|]); destruct Hin)) as UN2; clear Hfr end.
lazymatch type of HS with st_ok_pi _ _ _ _ (restrict _ ?mz) => rename mz into ms2 end.
assert (KA3 : forall a, sp0 - 112 <= a < 2 ^ 64 -> rdW W (ms_mem ms2) a = rdW W mA a).
{ intros a Ha. rewrite UN2 by (first [lia | tauto]). exact (KA2 a Ha). }
psrr_branch_tok RUN BR HS SHOK2 jBspan.
- (* i + 1 < n: back to the head *)
  rewrite branch_ne_U, U_SLit, (U_atom_off _ 23 (nW - Z.of_nat i) (-1)) in Hc;
    [| rewrite OLD2 by lia; rewrite (EE 23%nat 23%bv eq_refl); exact R23 | lia | lia].
  change (zcanon 0) with 0 in Hc. apply negb_true_iff, Z.eqb_neq in Hc.
  paj_run_to_tok RUNTO HS HJ2 SHOK2 jBspan PC_A.
  { apply awr_ok_cons_ro; [cbn; lia|]. apply awr_ok_nil. }
  lazymatch goal with Hfr : frame_of _ _ (mrestrict _ _) (mrestrict _ _) |- _ =>
  pose proof (kept_of_frame (segs := SEGS) _ _ _ _ _ (fun _ => False) Hfr
    ltac:(intros b wlo whi a Hin Hrr; vm_compute in Hin;
      repeat (destruct Hin as [Hq | Hin]; [injection Hq as <- <- <-; cbn [base_val ew ewset Nat.eqb] in Hrr; lia|]); destruct Hin)) as UN3; clear Hfr end.
  pmkst HS.
  prreg HS (2%bv : bv 5) T2. prreg HS (3%bv : bv 5) T3. prreg HS (4%bv : bv 5) T4. prreg HS (8%bv : bv 5) T8.
  prreg HS (9%bv : bv 5) T9. prreg HS (18%bv : bv 5) T18. prreg HS (19%bv : bv 5) T19. prreg HS (20%bv : bv 5) T20.
  prreg HS (21%bv : bv 5) T21. prreg HS (23%bv : bv 5) T23. prreg HS (24%bv : bv 5) T24. prreg HS (25%bv : bv 5) T25.
  rewrite ?OLD2 in T2, T3, T4, T8, T9, T18, T19, T20, T21, T23, T25 by lia.
  assert (T22 : getr (ms_regs ms0) 22 = w64 (SHADOW_OFF + (W0 + 24) / 8)).
  { jw_rawreg HS (22%bv : bv 5) Hr.
    rewrite Hr. rewrite (denot_shx _ 9 32 0 (W0 + 24) jSB); [unfold jSB; rewrite Z.add_0_r; reflexivity
    | cbn [ew ewset Nat.eqb]; rewrite ?OLD2 by lia; rewrite (EE 9%nat 9%bv eq_refl); exact R9
    | cbn [ew ewset Nat.eqb]; rewrite ?OLD2 by lia; exact E32 | lia | lia | lia | unfold jSB, SHADOW_OFF; lia]. }
  assert (T27 : getr (ms_regs ms0) 27 = w64 ((W0 + 16) / 8)).
  { jw_rawreg HS (27%bv : bv 5) Hr27.
    rewrite Hr27. rewrite (jw_srl3 _ 18 0 (W0 + 16));
    [ rewrite Z.add_0_r; reflexivity
    | cbn [ew ewset Nat.eqb]; rewrite ?OLD2 by lia; rewrite (EE 18%nat 18%bv eq_refl); exact R18 | lia | lia | lia]. }
  rewrite (EE 2%nat 2%bv eq_refl), R2 in T2. rewrite (EE 3%nat 3%bv eq_refl), R3 in T3. rewrite (EE 4%nat 4%bv eq_refl), R4 in T4.
  rewrite (EE 9%nat 9%bv eq_refl), R9 in T9. rewrite (EE 18%nat 18%bv eq_refl), R18 in T18.
  rewrite (EE 19%nat 19%bv eq_refl), R19 in T19. rewrite (EE 20%nat 20%bv eq_refl), R20 in T20.
  rewrite (EE 19%nat 19%bv eq_refl), R19 in T25. rewrite E32 in T21.
  rewrite (EE 8%nat 8%bv eq_refl), R8, E44, HQ2 in T8. rewrite (EE 23%nat 23%bv eq_refl), R23 in T23.
  assert (Hlen : astr_len (nth i ws []) = len) by reflexivity.
  unfold w64 in T8, T19, T23, T25. rewrite Hlen in T8. rewrite !unsigned_lit_small in T8, T19, T23, T25 by lia.
  rewrite alu_add_small in T8 by (unfold M64; lia).
  apply (IHk (Datatypes.S i) (ms_regs ms0) (ms_mem ms0) _ ltac:(lia) ltac:(lia)).
  split; [exact HJ2|].
  split; [apply (jw_frame_kept _ _ _ _ HFR); intros a Ha; rewrite UN3 by (first [lia | tauto]); exact (KA3 a ltac:(lia))|].
  split; [intros a Ha; rewrite UN3 by (first [lia | tauto]); rewrite KA3 by lia; exact (KA a Ha)|].
  split; [exact T2|]. split; [exact T3|]. split; [exact T4|].
  split; [rewrite T8; unfold w64; f_equal; rewrite ENS; fold ni; fold len; lia|].
  split; [exact T9|]. split; [exact T18|].
  split; [rewrite T19; unfold w64; f_equal; unfold p; lia|].
  split; [exact T20|].
  split; [rewrite T21; reflexivity|].
  split; [exact T22|].
  split; [rewrite T23; unfold w64; f_equal; lia|].
  split; [exact T24|].
  split; [rewrite T25; unfold w64; f_equal; unfold p; lia|].
  exact T27.
- (* i + 1 = n: the malloc call *)
  rewrite branch_ne_U, U_SLit, (U_atom_off _ 23 (nW - Z.of_nat i) (-1)) in Hc;
    [| rewrite OLD2 by lia; rewrite (EE 23%nat 23%bv eq_refl); exact R23 | lia | lia].
  change (zcanon 0) with 0 in Hc. apply negb_false_iff, Z.eqb_eq in Hc.
  paj_run_tok RUN HS HJ2 SHOK2 jBspan.
  { apply awr_ok_cons_ro; [cbn; lia|]. apply awr_ok_nil. }
  lazymatch goal with Hfr : frame_of _ _ (mrestrict _ _) (mrestrict _ _) |- _ =>
  pose proof (kept_of_frame (segs := SEGS) _ _ _ _ _ (fun _ => False) Hfr
    ltac:(intros b wlo whi a Hin Hrr; vm_compute in Hin;
      repeat (destruct Hin as [Hq | Hin]; [injection Hq as <- <- <-; cbn [base_val ew ewset Nat.eqb] in Hrr; lia|]); destruct Hin)) as UN3; clear Hfr end.
  assert (Hall : firstn (Datatypes.S i) ws = ws) by (apply firstn_all2; lia).
  pmkst HS.
  prreg HS (1%bv : bv 5) T1. prreg HS (2%bv : bv 5) T2. prreg HS (3%bv : bv 5) T3. prreg HS (4%bv : bv 5) T4.
  prreg HS (8%bv : bv 5) T8. prreg HS (9%bv : bv 5) T9. prreg HS (10%bv : bv 5) T10. prreg HS (18%bv : bv 5) T18.
  prreg HS (21%bv : bv 5) T21.
  rewrite ?OLD2 in T2, T3, T4, T8, T9, T10, T18, T21 by lia.
  assert (T22 : getr (ms_regs ms0) 22 = w64 (SHADOW_OFF + (W0 + 24) / 8)).
  { jw_rawreg HS (22%bv : bv 5) Hr.
    rewrite Hr. rewrite (denot_shx _ 9 32 0 (W0 + 24) jSB); [unfold jSB; rewrite Z.add_0_r; reflexivity
    | cbn [ew ewset Nat.eqb]; rewrite ?OLD2 by lia; rewrite (EE 9%nat 9%bv eq_refl); exact R9
    | cbn [ew ewset Nat.eqb]; rewrite ?OLD2 by lia; exact E32 | lia | lia | lia | unfold jSB, SHADOW_OFF; lia]. }
  assert (T27 : getr (ms_regs ms0) 27 = w64 ((W0 + 16) / 8)).
  { jw_rawreg HS (27%bv : bv 5) Hr27.
    rewrite Hr27. rewrite (jw_srl3 _ 18 0 (W0 + 16));
    [ rewrite Z.add_0_r; reflexivity
    | cbn [ew ewset Nat.eqb]; rewrite ?OLD2 by lia; rewrite (EE 18%nat 18%bv eq_refl); exact R18 | lia | lia | lia]. }
  rewrite (EE 2%nat 2%bv eq_refl), R2 in T2. rewrite (EE 3%nat 3%bv eq_refl), R3 in T3. rewrite (EE 4%nat 4%bv eq_refl), R4 in T4.
  rewrite (EE 9%nat 9%bv eq_refl), R9 in T9. rewrite (EE 18%nat 18%bv eq_refl), R18 in T18.
  rewrite E32 in T21.
  rewrite (EE 8%nat 8%bv eq_refl), R8, E44, HQ2 in T8, T10.
  assert (Hlen : astr_len (nth i ws []) = len) by reflexivity.
  unfold w64 in T8, T10. rewrite Hlen in T8, T10. rewrite !unsigned_lit_small in T8, T10 by lia.
  rewrite !alu_add_small in T8, T10 by (unfold M64; lia).
  assert (Esum : ni + len + 1 = PJoin.join_need ws) by (rewrite <- Hall, ENS; fold ni; fold len; lia).
  apply (jw_call (ms_regs ms0) (ms_mem ms0) _ (PJoin.join_need ws) [] HJ2).
  + apply (jw_frame_kept _ _ _ _ HFR). intros a Ha. rewrite UN3 by (first [lia | tauto]). exact (KA3 a ltac:(lia)).
  + intros a Ha. rewrite UN3 by (first [lia | tauto]). rewrite KA3 by lia. exact (KA a Ha).
  + exact T1. + exact T2. + exact T3. + exact T4.
  + rewrite T8. unfold w64. f_equal. lia.
  + pose proof (jw_need_nonneg ws). lia.
  + apply achain_low. pose proof (jw_need_nonneg ws). lia.
  + exact T9.
  + rewrite T10. unfold w64, jtot. f_equal. lia.
  + exact T18. + rewrite T21. reflexivity. + exact T22. + exact T27.
Qed.
(* the frame the prologue stored, read off the stack region of a symbolic state after the prologue: ra and s0..s11
   at sp0 - 8 .. sp0 - 104, and (B only) the spill of len at sp0 - 112 (`sd a1,16(sp)`, 0x88b8c) *)
Ltac jw_frame_ext HS Usp EE HFR :=
  let RF := fresh "RF" in let UspX := fresh "UspX" in
  lazymatch type of HS with
  | st_ok_pi _ _ ?Ex ?ssx (restrict _ ?msx) =>
    let r0 := eval vm_compute in (nth 0 (ss_mem ssx) got_regionP) in
    pose proof (st_ok_pi_region_nth Ex ssx (restrict _ msx) 0 r0 HS ltac:(vm_compute; reflexivity)) as RF;
    assert (UspX : bv_unsigned (ew Ex 2) = spZ regs) by (cbn [ew ewset Nat.eqb]; exact Usp)
  | st_ok _ ?Ex ?ssx (restrict _ ?msx) =>
    let r0 := eval vm_compute in (nth 0 (ss_mem ssx) got_regionP) in
    pose proof (st_ok_region_nth Ex ssx (restrict _ msx) 0 r0 HS ltac:(vm_compute; reflexivity)) as RF;
    assert (UspX : bv_unsigned (ew Ex 2) = spZ regs) by (cbn [ew ewset Nat.eqb]; exact Usp)
  end;
  cbn [ms_mem restrict] in RF;
  lazymatch type of RF with region_ok _ _ ?mm _ =>
  assert (HFR : jframe mm);
  [ split;
    [ intros j r Hj;
      assert (Hj13 : (j < 13)%nat) by (apply (proj1 (nth_error_Some j_saved j)); rewrite Hj; discriminate);
      do 13 (destruct j as [|j]; [cbn in Hj; injection Hj as <-;
        lazymatch goal with |- val_mem _ _ (_ - 8 - 8 * Z.of_nat ?K) 8 (bv_unsigned (getr _ (Z_to_bv 5 ?R))) =>
          let off := eval vm_compute in (-8 - 8 * Z.of_nat K) in
          let rn := eval vm_compute in (Z.to_nat R) in
          let V := fresh "V" in
          pose proof (field_of_region_any _ _ _ _ _ _ _ _ _ off 8%N (SOff rn 0) RF UspX
            ltac:(cbn [In]; repeat (first [left; reflexivity | right])) ltac:(cbn; lia)) as V;
          cbn [sv_denot ew ewset Nat.eqb] in V; rewrite Z.add_0_r, Z_to_bv_bv_unsigned in V;
          rewrite (EE rn (Z_to_bv 5 R) eq_refl) in V;
          change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64) in V;
          rewrite Z.mod_small in V by (pose proof (bv_unsigned_in_range 64 (getr regs (Z_to_bv 5 R))) as HR;
            change (bv_modulus 64) with (2 ^ 64) in HR; lia);
          replace (spZ regs - 8 - 8 * Z.of_nat K) with (spZ regs + off) by (cbn; lia); exact V
        end |]);
      lia
    | let VO := fresh "VO" in
      pose proof (field_of_region_any _ _ _ _ _ _ _ _ _ (-112) 8%N (SOff 11 0) RF UspX
        ltac:(cbn [In]; repeat (first [left; reflexivity | right])) ltac:(cbn; lia)) as VO;
      cbn [sv_denot ew ewset Nat.eqb] in VO; rewrite Z.add_0_r, Z_to_bv_bv_unsigned in VO;
      rewrite (EE 11%nat 11%bv eq_refl), H11 in VO;
      change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64) in VO;
      unfold w64 in VO; rewrite unsigned_lit_small in VO by lia;
      rewrite Z.mod_small in VO by lia;
      replace (spZ regs - 112) with (spZ regs + (-112)) by lia; exact VO ]
  | clear RF UspX ] end.
(* the entry (0x88b50 .. 0x88bc0): the prologue (with `sd a1,16(sp)`, the spill of len), the alignment check of w
   (0x88b90, refuted by W0 mod 8 = 0), the shadow base, the shadow check of w->n, then loop A (n > 0) or the malloc
   call of 1 byte (n = 0). On the n = 0 path s0 still holds the caller's value, so the malloc call reads afn_pre's
   own frame chain (Hch0) *)
Lemma jw_entry : SRr SEGS W (cfg_at SEGS (BASE + AF_joined) regs mem md) JPOST.
Proof.
jctx.
pose proof (@pa_B_ok _ _ PI) as HBASE. pose proof (pa_base_lo (L := cmd_listing)) as HBLO.
pose proof HNEED as HMX. unfold MALLOC_MAX in HMX.
pose proof alloc_ceiling_value as [HAC1 HAC2].
pose proof (ajournal_init SEGS B JOINED_STK FPj ly S W regs mem md ch HPRE) as HJ.
assert (Harr : 4096 <= arr <= alloc_ceiling).
{ destruct HAB as (b & m & Hbm & Hb1 & Hb2). destruct (al_blocks _ _ LAWS _ _ _ _ _ b m HAR0 Hbm) as (_ & Hb4 & Hbc & _ & _ & _ & Hm).
  pose proof (req_size_pos m (proj1 Hm)) as [Hm1 Hm2]. lia. }
assert (Hs0r : 0 <= s0Z regs < 2 ^ 64).
{ unfold s0Z. pose proof (bv_unsigned_in_range 64 (getr regs 8)) as HR.
  change (bv_modulus 64) with (2 ^ 64) in HR. lia. }
set (E := Eimg (Ereg regs [Z_to_bv 64 jSB; Z_to_bv 64 arr; Z_to_bv 64 nW])).
assert (HEI : img_env VAL A_LIM E) by apply Eimg_env.
assert (EE : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E n = getr regs r)
  by (intros n r Hn; apply ew_Eimg_Ereg_nat; exact Hn).
assert (EX : forall j, (j < 3)%nat -> ew E (32 + j) = nth j [Z_to_bv 64 jSB; Z_to_bv 64 arr; Z_to_bv 64 nW] (Z_to_bv 64 0)).
{ intros j Hj. unfold E. rewrite Eimg_low by (unfold A_TEXT; lia). apply ew_Ereg_extra. }
assert (E32 : ew E 32 = Z_to_bv 64 jSB) by exact (EX 0%nat ltac:(lia)).
assert (E33 : ew E 33 = Z_to_bv 64 arr) by exact (EX 1%nat ltac:(lia)).
assert (E34 : ew E 34 = Z_to_bv 64 nW) by exact (EX 2%nat ltac:(lia)).
assert (Usp : bv_unsigned (ew E 2) = sp0) by (rewrite (EE 2%nat 2%bv eq_refl); reflexivity).
assert (U10 : bv_unsigned (ew E 10) = W0) by (rewrite (EE 10%nat 10%bv eq_refl), H10; apply unsigned_lit_small; lia).
assert (E241 : ew E (A_OBJ 0) = Z_to_bv 64 (VAL (A_OBJ 0))) by (unfold E; apply Eimg_img; unfold A_OBJ, A_TEXT, A_LIM; lia).
assert (E253 : ew E (A_OBJ 12) = Z_to_bv 64 (VAL (A_OBJ 12))) by (unfold E; apply Eimg_img; unfold A_OBJ, A_TEXT, A_LIM; lia).
pose proof (pa_val_range (A_OBJ 0)) as RG0. pose proof (pa_val_range (A_OBJ 12)) as RG12.
assert (U241 : bv_unsigned (ew E (A_OBJ 0)) = VAL (A_OBJ 0)) by (rewrite E241; apply unsigned_lit_small; lia).
assert (U253 : bv_unsigned (ew E (A_OBJ 12)) = VAL (A_OBJ 12)) by (rewrite E253; apply unsigned_lit_small; lia).
pose proof (pa_obj_img 12 ltac:(lia)) as HcellR. pose proof (pa_obj_img 0 ltac:(lia)) as HgotR. pose proof (pal_got_cell B TL) as HgcD.
destruct (al_const _ _ LAWS _ _ _ _ _ HAR0) as (Kcell & _ & Kgot & _).
rewrite (pal_got_shadow B TL), (pal_cell B TL) in Kgot. rewrite (pal_cell B TL) in Kcell.
assert (HS : st_ok_pi SEGS VAL E ssE (restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + AF_joined)) mem (seg_rom SEGS)))).
{ rewrite restrict_mkst_fx. unfold ssE. apply pa_entry_st_ok_full.
  - apply regs_ok_Eimg_Ereg.
  - vm_compute. reflexivity.
  - unfold stack_region, got_regionP, bcell_regionP, j_struct.
    repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
    + rewrite Usp. split; [lia|]. split; [lia|]. split; [|constructor].
      intros o Ho. apply (apresent_writable SEGS). apply Hpres0. lia.
    + rewrite U241. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
      constructor; [|constructor].
      apply (chunk_ok_val SEGS E _ (VAL (A_OBJ 0)) 0 8 (SOff (A_OBJ 12) 0) (VAL (A_OBJ 12)));
        [cbn [sv_denot]; rewrite E253, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); lia | cbn; lia |].
      rewrite Z.add_0_r. exact (val_mem_of_rdword SEGS _ _ _ _ Kgot).
    + rewrite U253. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
      constructor; [|constructor].
      apply (chunk_ok_val SEGS E _ (VAL (A_OBJ 12)) 0 8 (SOff 32 0) jSB);
        [cbn [sv_denot]; rewrite E32, Z.add_0_r; rewrite unsigned_lit_small by (unfold jSB, SHADOW_OFF; lia); reflexivity
        | unfold jSB, SHADOW_OFF; cbn; lia | cbn; lia |].
      rewrite Z.add_0_r. exact (val_mem_of_rdword SEGS _ _ _ _ Kcell).
    + rewrite U10. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
      constructor; [|constructor; [|constructor]].
      * apply (chunk_ok_val SEGS E _ W0 16 8 (SOff 33 0) arr);
          [cbn [sv_denot]; rewrite E33, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | cbn; lia | cbn; lia |].
        exact (jw_val_of_aval _ _ _ _ _ HVA).
      * apply (chunk_ok_val SEGS E _ W0 24 4 (SOff 34 0) nW);
          [cbn [sv_denot]; rewrite E34, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | cbn; lia | cbn; lia |].
        exact (jw_val_of_aval _ _ _ _ _ HVN).
  - apply pairwise_disjoint_of_extents. unfold stack_region, got_regionP, bcell_regionP, j_struct, extent_of_region.
    cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite Usp, U241, U253, U10.
    cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd]. repeat split; lia.
  - split; [|split; exact I]. cbn [f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
    rewrite Usp, U10, E32, E33, E34. rewrite !unsigned_lit_small by (unfold jSB, SHADOW_OFF; lia).
    unfold jstklo, jstkhi, jheaphi, jSB. change (2 ^ 4) with 16. change (2 ^ 3) with 8.
    rewrite Z.pow_0_r, !Z.mod_1_r.
    repeat split; first [exact I | exact HW8 | exact HARR8 | lia]. }
assert (UB : U E jBx = SHADOW_OFF) by (unfold jBx; apply U_atom; [rewrite E32; reflexivity | unfold SHADOW_OFF; lia]).
assert (SHOK : sh_ok SEGS jBx [mkSHE 10 16 28] E (mrestrict (w_H W) mem)).
{ unfold sh_ok. apply Forall_cons; [|apply Forall_nil].
  unfold shent_ok, app_apart. cbn [she_m she_lo she_hi].
  assert (U10' : U E (SOff 10 0) = W0) by (apply U_atom; [rewrite (EE 10%nat 10%bv eq_refl); exact H10 | lia]).
  rewrite UB, U10', <- (aview_rd_of SEGS). split.
  - exact HWR.
  - intros a Ha. unfold kLowShadowBeg, kHighMemBeg, SHADOW_OFF in *. lia. }
unfold cfg_at. change (w64 (BASE + AF_joined)) with (Z_to_bv 64 (BASE + AF_joined)).
paj_run_tok RUN HS HJ SHOK jBspan.
{ unfold ssE. cbn [ss_mem].
  eapply awr_ok_cons_stack; [reflexivity | exact Usp | cbn; rewrite HJS; lia | cbn; lia |].
  repeat (apply awr_ok_cons_ro; [cbn; lia|]). apply awr_ok_nil. }
lazymatch goal with Hfr : frame_of _ _ (mrestrict _ _) (mrestrict _ _) |- _ =>
pose proof (kept_of_frame (segs := SEGS) _ _ _ _ _ (fun a => sp0 - 128 <= a < sp0) Hfr
  ltac:(intros b wlo whi a Hin Hrr; vm_compute in Hin;
    repeat (destruct Hin as [Hq | Hin]; [injection Hq as <- <- <-; cbn [base_val ew ewset Nat.eqb] in Hrr; rewrite ?Usp, ?U241, ?U253, ?U10 in Hrr; lia|]); destruct Hin)) as UN1; clear Hfr end.
psrr_branch_tok RUN BR HS SHOK jBspan.
- (* n = 0: malloc(1) *)
  rewrite (jw_branch_ge _ _ _ 0 nW) in Hc; [| reflexivity | cbn [sv_denot ew ewset Nat.eqb]; rewrite E34, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | lia | lia].
  apply Z.leb_le in Hc. assert (Hws : ws = []) by (destruct ws as [|wz ws']; [reflexivity | cbn [length] in Hc; lia]).
  paj_run_tok RUN HS HJ SHOK jBspan.
  { unfold ssE. cbn [ss_mem].
    eapply awr_ok_cons_stack; [reflexivity | cbn [ew ewset Nat.eqb]; exact Usp | cbn; rewrite HJS; lia | cbn; lia |].
    repeat (apply awr_ok_cons_ro; [cbn; lia|]). apply awr_ok_nil. }
  lazymatch goal with Hfr : frame_of _ _ (mrestrict _ _) (mrestrict _ _) |- _ =>
  pose proof (kept_of_frame (segs := SEGS) _ _ _ _ _ (fun a => sp0 - 128 <= a < sp0) Hfr
    ltac:(intros b wlo whi a Hin Hrr; vm_compute in Hin;
      repeat (destruct Hin as [Hq | Hin]; [injection Hq as <- <- <-; cbn [base_val ew ewset Nat.eqb] in Hrr; rewrite ?Usp, ?U241, ?U253, ?U10 in Hrr; lia|]); destruct Hin)) as UN2; clear Hfr end.
  pmkst HS.
  prreg HS (1%bv : bv 5) T1. prreg HS (2%bv : bv 5) T2. prreg HS (3%bv : bv 5) T3. prreg HS (4%bv : bv 5) T4.
  prreg HS (8%bv : bv 5) T8. prreg HS (9%bv : bv 5) T9. prreg HS (10%bv : bv 5) T10. prreg HS (18%bv : bv 5) T18.
  prreg HS (21%bv : bv 5) T21.
  jw_rawreg HS (22%bv : bv 5) T22.
  rewrite (denot_shx _ 10 32 24 W0 jSB) in T22;
    [| cbn [ew ewset Nat.eqb]; rewrite (EE 10%nat 10%bv eq_refl); exact H10 | cbn [ew ewset Nat.eqb]; exact E32 | lia | lia | lia | unfold jSB, SHADOW_OFF; lia].
  jw_rawreg HS (27%bv : bv 5) T27.
  rewrite (jw_srl3 _ 10 16 W0) in T27;
    [| cbn [ew ewset Nat.eqb]; rewrite (EE 10%nat 10%bv eq_refl); exact H10 | lia | lia | lia].
  jw_frame_ext HS Usp EE HFRx.
  apply (jw_call _ _ _ (s0Z regs) ch HJ HFRx).
  + intros a Ha. rewrite UN2 by (first [lia | tauto]). apply UN1; lia.
  + exact T1.
  + rewrite T2, Usp. unfold w64; f_equal; lia.
  + rewrite T3, (EE 3%nat 3%bv eq_refl). exact Hgp0.
  + rewrite T4, (EE 4%nat 4%bv eq_refl). exact Htp0.
  + rewrite T8, (EE 8%nat 8%bv eq_refl). unfold s0Z, w64. rewrite Z_to_bv_bv_unsigned. reflexivity.
  + exact Hs0r.
  + exact Hch0.
  + rewrite T9, U10. reflexivity.
  + rewrite T10. unfold jtot. rewrite Hws. reflexivity.
  + rewrite T18, U10. reflexivity.
  + rewrite T21, E32. reflexivity.
  + rewrite T22. reflexivity.
  + rewrite T27. reflexivity.
- (* n > 0: loop A from word 0 *)
  rewrite (jw_branch_ge _ _ _ 0 nW) in Hc; [| reflexivity | cbn [sv_denot ew ewset Nat.eqb]; rewrite E34, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | lia | lia].
  apply Z.leb_gt in Hc.
  paj_run_to_tok RUNTO HS HJ SHOK jBspan PC_A.
  { unfold ssE. cbn [ss_mem].
    eapply awr_ok_cons_stack; [reflexivity | cbn [ew ewset Nat.eqb]; exact Usp | cbn; rewrite HJS; lia | cbn; lia |].
    repeat (apply awr_ok_cons_ro; [cbn; lia|]). apply awr_ok_nil. }
  lazymatch goal with Hfr : frame_of _ _ (mrestrict _ _) (mrestrict _ _) |- _ =>
  pose proof (kept_of_frame (segs := SEGS) _ _ _ _ _ (fun a => sp0 - 128 <= a < sp0) Hfr
    ltac:(intros b wlo whi a Hin Hrr; vm_compute in Hin;
      repeat (destruct Hin as [Hq | Hin]; [injection Hq as <- <- <-; cbn [base_val ew ewset Nat.eqb] in Hrr; rewrite ?Usp, ?U241, ?U253, ?U10 in Hrr; lia|]); destruct Hin)) as UN2; clear Hfr end.
  pmkst HS.
  prreg HS (2%bv : bv 5) T2. prreg HS (3%bv : bv 5) T3. prreg HS (4%bv : bv 5) T4. prreg HS (8%bv : bv 5) T8.
  prreg HS (9%bv : bv 5) T9. prreg HS (18%bv : bv 5) T18. prreg HS (19%bv : bv 5) T19. prreg HS (20%bv : bv 5) T20.
  prreg HS (21%bv : bv 5) T21. prreg HS (24%bv : bv 5) T24. prreg HS (25%bv : bv 5) T25.
  jw_rawreg HS (22%bv : bv 5) T22.
  rewrite (denot_shx _ 10 32 24 W0 jSB) in T22;
    [| cbn [ew ewset Nat.eqb]; rewrite (EE 10%nat 10%bv eq_refl); exact H10 | cbn [ew ewset Nat.eqb]; exact E32 | lia | lia | lia | unfold jSB, SHADOW_OFF; lia].
  jw_rawreg HS (27%bv : bv 5) T27.
  rewrite (jw_srl3 _ 10 16 W0) in T27;
    [| cbn [ew ewset Nat.eqb]; rewrite (EE 10%nat 10%bv eq_refl); exact H10 | lia | lia | lia].
  jw_rawreg HS (23%bv : bv 5) T23.
  rewrite (jw_sgtz_and _ 34 nW) in T23; [| cbn [ew ewset Nat.eqb]; exact E34 | lia].
  jw_frame_ext HS Usp EE HFRx.
  apply (jw_loopA (length ws) 0 _ _ _ ltac:(lia) ltac:(lia)).
  split; [exact HJ|]. split; [exact HFRx|].
  split; [intros a Ha; rewrite UN2 by (first [lia | tauto]); apply UN1; lia|].
  split; [rewrite T2, Usp; unfold w64; f_equal; try lia|].
  split; [rewrite T3, (EE 3%nat 3%bv eq_refl); exact Hgp0|].
  split; [rewrite T4, (EE 4%nat 4%bv eq_refl); exact Htp0|].
  split; [rewrite T8; reflexivity|].
  split; [rewrite T9, U10; reflexivity|].
  split; [rewrite T18, U10; reflexivity|].
  split; [rewrite T19, E33; unfold w64; f_equal; try lia|].
  split; [rewrite T20, E33; unfold w64; f_equal; try lia|].
  split; [rewrite T21, E32; reflexivity|].
  split; [rewrite T22; reflexivity|].
  split; [rewrite T23; unfold w64; f_equal; try lia|].
  split; [rewrite T24; reflexivity|].
  split; [rewrite T25, E33; unfold w64; f_equal; try lia|].
  rewrite T27. reflexivity.
Qed.
End ctx.
(* tjoined_spec (lib/B/Prog/joined_c.v) with the premises on *len last. On this build s0 at the malloc call
   (0x88c48) is the running length, not len, so the frame chain the malloc
   rule reads comes from afn_pre's own chain (n = 0) or from achain_low (n > 0), a Theorem Labs lane's PASS4-REFIT.md
   section B. The alignment premises W0 mod 8 = 0 and arr mod 8 = 0 ARE used here: they refute the UBSan traps
   0x88b90 and 0x88c08 / 0x88cc8 / 0x88d3c. *)
Theorem tjoined_core : forall ly S W (regs : bvmap 5 word) mem md ch (W0 arr outp : Z) (wp : list Z) (ws : list (list byte)),
afn_pre SEGS B JOINED_STK ly S W regs mem md ch ->
arodata_okP SEGS RLO RHI B (rdW W mem) ->
getr regs 10 = w64 W0 -> getr regs 11 = w64 outp ->
spZ regs <= W0 + 16 -> W0 + 32 <= ly_stk_hi ly -> W0 mod 8 = 0 ->
length wp = length ws -> Z.of_nat (length ws) < 2 ^ 31 ->
aval_mem (rdW W mem) (W0 + 24) 4 (Z.of_nat (length ws)) ->
aval_mem (rdW W mem) (W0 + 16) 8 arr -> 0 <= arr < 2 ^ 64 -> arr mod 8 = 0 ->
in_blockA (ablocks B ly S) arr (8 * Z.of_nat (length ws)) ->
(forall k, (k < length ws)%nat ->
 aval_mem (rdW W mem) (arr + 8 * Z.of_nat k) 8 (nth k wp 0) /\ 0 <= nth k wp 0 < 2 ^ 64 /\
 in_blockA (ablocks B ly S) (nth k wp 0) (Z.of_nat (length (nth k ws [])) + 1) /\
 astr_atR (rdW W mem) (nth k wp 0) (nth k ws [])) ->
PJoin.join_need ws + 1 < MALLOC_MAX ->
spZ regs <= outp -> outp + 8 <= ly_top ly -> outp mod 8 = 0 ->
(outp + 8 <= W0 + 16 \/ W0 + 32 <= outp) ->
st_nev S + EV_JOINED <= EV_MAX -> blocks_bytes S + LIVE_JOINED <= LIVE_MAX ->
mo_ok MT S (XM_JOINED MT ws) ->
(forall i, 0 <= i < 8 -> apresent (w_H W) mem (outp + i)) ->
SRr SEGS W (cfg_at SEGS (BASE + AF_joined) regs mem md)
(apost_base SEGS B JOINED_STK [(outp, outp + 8)] regs ly S W mem md EV_JOINED
(fun ly' S' W' regs' mem' md' => exists res : Z,
 getr regs' 10 = w64 res /\ 4096 <= res < 2 ^ 64 /\
 Permutation (ablocks B ly' S') ((res, PJoin.join_need ws + 1) :: ablocks B ly S) /\
 Forall (fun qk => iv_apart res (PJoin.join_need ws + 1) (fst qk) (snd qk)) (ablocks B ly S) /\
 in_blockA (ablocks B ly' S') res (PJoin.join_need ws + 1) /\
 abytes_atR (rdW W' mem') res (join_sp ws ++ [Z_to_bv 8 0]) /\
 aval_mem (rdW W' mem') outp 8 (Z.of_nat (length (join_sp ws))) /\
 (forall p n i, In (p, n) (ablocks B ly S) -> 0 <= i < n -> rdW W' mem' (p + i) = rdW W mem (p + i)) /\
 blocks_bytes S' <= blocks_bytes S + LIVE_JOINED /\
 mo_le MT S S' (XM_JOINED MT ws))).
Proof.
intros ly S W regs mem md ch W0 arr outp wp ws HPRE HROD H10 H11 HW1 HW2 HW8 HLEN HN31 HVN HVA HARR HARR8 HAB HWS
  HNEED HO1 HOTOP HO3 HOS HEV HLIVE MOK HOPR.
pose proof HPRE as (HAR & _ & _ & _ & _ & Hstk & _).
pose proof Hstk as (_ & HSTK0 & _ & Hslo & _ & _ & _ & _ & Htop2).
assert (HWR : range_addressable (rdW W mem) SHADOW_OFF (W0 + 16) 12) by (apply (jw_stack_ra ly S W mem md); [exact HAR | lia | lia]).
assert (HO2 : outp + 8 <= ly_stk_hi ly) by lia.
eapply (jw_entry ly S W regs mem md ch W0 arr outp wp ws); eassumption.
Qed.
(* the statement: tjoined_core with the premises in the statement's order *)
Theorem tjoined_spec_holds : tjoined_spec B MT.
Proof.
unfold tjoined_spec.
intros ly S W regs mem md ch W0 arr outp wp ws HPRE HROD H10 H11 HW1 HW2 HW8 HLEN HN31 HVN HVA HARR HARR8 HAB HWS
  HNEED HO1 HOTOP HO3 HOS HOPR HEV HLIVE MOK.
exact (tjoined_core ly S W regs mem md ch W0 arr outp wp ws HPRE HROD H10 H11 HW1 HW2 HW8 HLEN HN31 HVN HVA HARR
  HARR8 HAB HWS HNEED HO1 HOTOP HO3 HOS HEV HLIVE MOK HOPR).
Qed.
End e.
End d.
End b.
