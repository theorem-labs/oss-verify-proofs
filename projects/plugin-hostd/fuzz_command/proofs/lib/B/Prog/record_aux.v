(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: the parts of record's ASan+UBSan walk (plugin-hostd/fuzz_command,
   fuzz_command.asan-ubsan) that need no callee statement and no image: the walk's points in B's listing, the listing's
   62 slots, the symbolic states of the entry and of the meet of record()'s two arms, the slot, the footprint, and the
   recorder's representation under record()'s stores. After A's inlined record() in lib/A/Prog/sup_pin_accept_s4.v
   (a working branch 3cc8391594b: spa_acall_new, spa_rep_record_lt, spa_rep_spill_fn, spa_rep_ncalls) and
   lib/A/Prog/sup_pin_accept_r.v (spa_arep_rest, spa_arep_keep), re-derived on B's code (below). A's record() is
   inlined in every recording function; B keeps it as a function, so there is no A walk of it. The Generation-N
   walk lib/B/Prog/record.v of a working branch 543f2c3645b was read as a B-code template only, not ported. *)

(* record on B (recorder.c:205-221; entry BASE + AF_record = 0x8a728, .symtab LOCAL FUNC, 248 bytes, 62 instructions;
   measured with capstone 5.0.7 on fuzz_command.asan-ubsan, sha256 658cefbe806b535ba1fbe5a37c8efe02099fc39c...;
   listing lib/B/Prog/CmdList.v:4301-4362):
     0x8a728 .. 0x8a738  addi sp,sp,-32; sd ra,24(sp); sd s0,16(sp); sd s1,8(sp); sd s2,0(sp)
     0x8a73c .. 0x8a740  auipc a1; ld a3,-0x7ec(a1)    the shadow-base GOT word 0xa5f50 (listing PLdHi a3 a1 116 (A_OBJ 0))
     0x8a744 .. 0x8a748  auipc a1; addi a1,a1,-0x484   g_rec 0x5e32c0 (PAddHi a1 a1 117 (A_OBJ 44))
     0x8a74c .. 0x8a758  lw a2,8(a1) (ncalls); ld s2,0(a3) (the shadow base); li a3,16; mv s0,a0 (fn)
     0x8a75c             bne a2,a3 -> 0x8a778          record()'s two arms
     spill arm: 0x8a760 .. 0x8a76c  auipc a0; mv s1,a0 (record.spill 0x5e3760, PAddHi s1 a0 118 (A_OBJ 53)); li a1,1;
                0x8a770  jal rec_calls_free (0x89a4c); 0x8a774  j 0x8a7ac
     table arm: 0x8a778  addiw a0,a2,1; 0x8a77c  blt a0,a2 -> unimp 0x8a7fc (UBSan: ncalls++ overflow);
                0x8a780 .. 0x8a784  li a3,17; sw a0,8(a1) (ncalls := ncalls + 1);
                0x8a788  bgeu a2,a3 -> unimp (UBSan: index bound of g_rec.calls[ncalls]);
                0x8a78c .. 0x8a79c  a0 := 56 * ncalls; a2 := ~(g_rec + 16);
                0x8a7a0  bltu a2,a0 -> unimp (UBSan: pointer overflow of g_rec.calls + ncalls);
                0x8a7a4 .. 0x8a7a8  s1 := g_rec + 16 + 56 * ncalls
     meet:      0x8a7ac .. 0x8a7b0  andi a0,s1,7; bnez a0 -> unimp (UBSan: alignment of c)
                0x8a7b4 .. 0x8a7c0  shadow byte of c; bnez -> 0x8a800 (0x8a804 blt -> 0x8a7c4, else 0x8a80c
                                    jal __asan_report_store4)
                0x8a7c4             sw s0,0(s1) (c->fn := fn)
                0x8a7c8 .. 0x8a7d8  shadow byte of c + 4; bnez -> 0x8a810 (0x8a818 blt -> 0x8a7dc, else 0x8a81c
                                    jal __asan_report_store4)
                0x8a7dc             sw zero,4(s1) (c->nargs := 0)
                0x8a7e0 .. 0x8a7f8  mv a0,s1; ld ra, s0, s1, s2; addi sp,sp,32; ret
   Calls: rec_calls_free 0x89a4c (from 0x8a770); __asan_report_store4 0x5ebf4 (from 0x8a80c and 0x8a81c, both
   unreached). UBSan is in trap mode: four trap branches 0x8a77c, 0x8a788, 0x8a7a0, 0x8a7b0, all to the one unimp
   0x8a7fc; no __ubsan_handle_* call. The three auipc (0x8a73c, 0x8a744, 0x8a760) form the GOT word's, g_rec's and
   record.spill's addresses as object atoms (A_OBJ 0, 44, 53, whose values cmd_val_objs gives); the A_HI values
   (116, 117, 118) are dead, and no load or store goes through an A_HI base, so the walk needs no cmd_val_his. *)
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require YZ00.
From Stdlib Require Import String ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YN3v YI00 YI04 YG0s.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YI16 YM05 YC5d YG0q.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B Require Import YF0m.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Rt Require Import RtDefs.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require Import RecFacts RecModel RecInv.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import PaTable PaSym PaStep PaRun PaShadow PaJournal.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import CmdSyms CmdAddr CmdList CmdPa CmdPaLib.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import
PaCall PaCallRun PaLibF PaLibG PaLibH PaSB PaDenot PaNoChain.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import CmdGlob CmdBase CmdChk CmdRep CmdObj CmdRo.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import CmdRecBase CmdRecCells CmdZsh.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import RecBLemmas RecBridge.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import rec_calls_free_c record_c CmdRecAns.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.

(* ---------- the walk's points in the listing ---------- *)
Definition RCB_E : Z := AF_record.               (* the entry (0x8a728) *)
Definition RCB_FRAME : Z := 32.
Definition RCB_RET_RCF : Z := AF_record + 0x4c.  (* j 0x8a7ac, after the call of rec_calls_free (0x8a774) *)
Definition RCB_MEET : Z := AF_record + 0x84.     (* andi a0,s1,7: the two arms meet (0x8a7ac) *)

(* the function's 62 slots in B's listing (lib/B/Prog/CmdList.v:4301-4362) *)
Definition rcb_code : ptable csym := [
PW 0xfe010113; PW 0x113c23; PW 0x813823; PW 0x913423; PW 0x1213023;
PHi (11%bv : bv 5) 116; PLdHi (13%bv : bv 5) (11%bv : bv 5) 116 (A_OBJ 0) 0x0 SZ8 true;
PHi (11%bv : bv 5) 117; PAddHi (11%bv : bv 5) (11%bv : bv 5) 117 (A_OBJ 44) 0x0;
PW 0x85a603; PW 0x6b903; PW 0x1000693; PW 0x50413; PW 0xd61e63;
PHi (10%bv : bv 5) 118; PAddHi (9%bv : bv 5) (10%bv : bv 5) 118 (A_OBJ 53) 0x0;
PW 0x100593; PW 0x48513; PCall CS_rec_calls_free (1%bv : bv 5); PW 0x380006f;
PW 0x16051b; PW 0x8c54063; PW 0x1100693; PW 0xa5a423; PW 0x6d67a63; PW 0x361513; PW 0x661613;
PW 0x40a60533; PW 0x1058613; PW 0xfff64613; PW 0x4a66e63; PW 0xa58533; PW 0x1050493;
PW 0x74f513; PW 0x4051663; PW 0x34d593; PW 0x12585b3; PW 0x58583; PW 0x4059063; PW 0x84a023;
PW 0x448513; PW 0x355593; PW 0x12585b3; PW 0x58583; PW 0x2059c63; PW 0x4a223; PW 0x48513;
PW 0x1813083; PW 0x1013403; PW 0x813483; PW 0x13903; PW 0x2010113; PW 0x8067; PW 0xc0001073;
PW 0x350513; PW 0xfcb540e3; PW 0x48513; PCall CS___asan_report_store4 (1%bv : bv 5);
PW 0x757613; PW 0x360613; PW 0xfcb642e3; PCall CS___asan_report_store4 (1%bv : bv 5)].

Lemma rcb_listing : firstn 62 (skipn (Z.to_nat (RCB_E / 4)) cmd_listing) = rcb_code.
Proof. vm_compute. reflexivity. Qed.

Lemma rcb_callees :
cmd_sigma CS_record = 0x8a728 /\ cmd_sigma CS_rec_calls_free = 0x89a4c /\ cmd_text + RCB_E = 0x8a728 /\
cmd_af CS_rec_calls_free = AF_rec_calls_free.
Proof. vm_compute. repeat split; reflexivity. Qed.

(* ---------- the symbolic state of the entry segment ---------- *)
(* atoms: the 32 registers, 32 = the shadow base, 33 = g_rec.ncalls; regions: the 32-byte frame below the entry sp
   (atom 2), the GOT word of the shadow-base cell, that cell, and g_rec.ncalls *)
Definition SA_SB : nat := 32.
Definition SA_N : nat := 33.
Definition rcb_ncalls : YP09.region :=
YP09.mkRegion (Some (A_OBJ 44)) OFF_NCALLS (OFF_NCALLS + 4) OFF_NCALLS (OFF_NCALLS + 4)
  [YP09.mkChunk OFF_NCALLS (CVal 4 (SOff SA_N 0))].
Definition rcb_rsA : smem := [stack_region RCB_FRAME; got_regionP; bcell_regionP SA_SB; rcb_ncalls].
Definition rcb_factsA : facts :=
mkFacts [(2%nat, mkAF (2 ^ 46) (2 ^ 47) 4); (SA_SB, mkAF SB SB 0); (SA_N, mkAF 0 16 0);
         (A_OBJ 44, mkAF A_G_REC A_G_REC 3)] [] [].
Definition ss_rcbA : sstate := mkSS RCB_E sr_atoms rcb_rsA None rcb_factsA.
Definition rcb_BxA : sv := SOff SA_SB 0.
Definition rcb_extraA (n : Z) : list word := [Z_to_bv 64 SB; Z_to_bv 64 n].
Definition rcb_Bspan : Z * Z := (SB, SB + 2 ^ 44 - 1).

(* ---------- the symbolic state where record()'s two arms meet (0x8a7ac) ---------- *)
(* atoms above the registers: 32 = the shadow base, 33 = the slot c, 34 .. 37 = the entry's ra, s0, s1, s2 (the
   frame's words); registers: s1 = c, s2 = the shadow base, sp = the entry sp - 32, s0 = fn (atom 8) *)
Definition SA_C : nat := 33.
Definition rcb_saved : list Z := [1; 8; 9; 18].
Definition rcb_extra (regs : bvmap 5 word) (c : Z) : list word :=
map (Z_to_bv 64) [SB; c] ++ map (fun r => getr regs (Z_to_bv 5 r)) rcb_saved.
Definition rcb_mframe : YP09.region :=
YP09.mkRegion (Some 2%nat) 0 RCB_FRAME 0 0
  [YP09.mkChunk 24 (CVal 8 (SOff 34 0)); YP09.mkChunk 16 (CVal 8 (SOff 35 0));
   YP09.mkChunk 8 (CVal 8 (SOff 36 0)); YP09.mkChunk 0 (CVal 8 (SOff 37 0))].
(* the slot: the walk writes its fn and nargs fields, and reads nothing of it *)
Definition rcb_mslot : YP09.region := YP09.mkRegion (Some SA_C) 0 CALL_SIZE 0 8 [].
Definition rcb_mrs : smem := [rcb_mframe; rcb_mslot].
Definition rcb_mregs : list sv := Eval vm_compute in sr_set (sr_set sr_atoms 9 (SOff SA_C 0)) 18 (SOff SA_SB 0).
Definition rcb_facts : facts :=
mkFacts [(2%nat, mkAF (2 ^ 46) (2 ^ 47) 4); (SA_SB, mkAF SB SB 0); (SA_C, mkAF (A_G_REC + OFF_CALLS) A_REC_SPILL 3)] [] [].
Definition ss_meet : sstate := mkSS RCB_MEET rcb_mregs rcb_mrs None rcb_facts.
Definition rcb_Bx : sv := SOff SA_SB 0.
Definition rcb_SH : list shent := [mkSHE SA_C 0 CALL_SIZE].

(* ---------- the slot ---------- *)
Definition rcb_slot_ok (c : Z) : Prop :=
(A_G_REC + OFF_CALLS <= c /\ c + CALL_SIZE <= A_G_REC + REC_SIZE /\ c mod 8 = 0) \/ c = A_REC_SPILL.

Lemma rcb_slot_bounds : forall c, rcb_slot_ok c ->
A_G_REC + OFF_CALLS <= c <= A_REC_SPILL /\ c mod 8 = 0 /\ c + CALL_SIZE <= A_REC_SPILL + SC_SIZE.
Proof.
intros c [(H1 & H2 & H3) | ->]; unfold A_G_REC, A_REC_SPILL, OFF_CALLS, REC_SIZE, CALL_SIZE, SC_SIZE in *;
[split; [lia | split; [exact H3 | lia]] | split; [lia | split; [reflexivity | lia]]].
Qed.

Lemma rcb_rec_slot_ok : forall R, (length (r_calls R) <= 16)%nat -> rcb_slot_ok (rec_slot R).
Proof.
intros R H. unfold rec_slot. destruct (Nat.ltb_spec (length (r_calls R)) 16) as [L|L]; [left | right; reflexivity].
unfold A_G_REC, OFF_CALLS, CALL_SIZE, REC_SIZE. split; [lia|]. split; [lia|].
apply Z.mod_divide; [lia|]. exists (771674 + 7 * Z.of_nat (length (r_calls R))). lia.
Qed.

Lemma rcb_grec_in : forall a, A_G_REC <= a < A_G_REC + REC_SIZE -> Exists (in_zr a) TFIB_PROG_STATIC.
Proof. intros a Ha. apply Exists_cons_hd. unfold in_zr. cbn [fst snd]. unfold A_G_REC, REC_SIZE in Ha. lia. Qed.

Lemma rcb_spill_in : forall a, A_REC_SPILL <= a < A_REC_SPILL + SC_SIZE -> Exists (in_zr a) TFIB_PROG_STATIC.
Proof.
intros a Ha. apply Exists_cons_tl. apply Exists_cons_hd. unfold in_zr. cbn [fst snd].
unfold A_REC_SPILL, SC_SIZE in Ha. lia.
Qed.

Lemma rcb_in_PG : forall c a, rcb_slot_ok c -> c <= a < c + CALL_SIZE -> Exists (in_zr a) TFIB_PROG_STATIC.
Proof.
intros c a Hc Ha. destruct Hc as [(H1 & H2 & _) | ->].
- apply rcb_grec_in. unfold A_G_REC, OFF_CALLS, REC_SIZE, CALL_SIZE in *. lia.
- apply rcb_spill_in. unfold SC_SIZE, CALL_SIZE in *. lia.
Qed.

Lemma rcb_PG_grec : forall a, A_G_REC <= a < A_G_REC + REC_SIZE -> inFP cmd_PG a.
Proof. intros a Ha. exists (A_G_REC, A_G_REC + 960). split; [left; reflexivity | cbn [fst snd]; unfold REC_SIZE in Ha; lia]. Qed.

Lemma rcb_PG_slot : forall c a, rcb_slot_ok c -> c <= a < c + CALL_SIZE -> inFP cmd_PG a.
Proof.
intros c a Hc Ha. destruct Hc as [(H1 & H2 & _) | ->].
- apply rcb_PG_grec. unfold A_G_REC, OFF_CALLS, REC_SIZE, CALL_SIZE in *. lia.
- exists (A_REC_SPILL, A_REC_SPILL + 56). split; [right; left; reflexivity | cbn [fst snd]; unfold CALL_SIZE in Ha; lia].
Qed.

(* the bytes the representation reads besides the recorder's blocks: g_rec and record.spill *)
Definition rcb_in_rec (a : Z) : Prop := A_G_REC <= a < A_G_REC + REC_SIZE \/ A_REC_SPILL <= a < A_REC_SPILL + SC_SIZE.

(* ---------- the recorder's representation under record()'s stores (A's sup_pin_accept_s4.v forms) ---------- *)

(* a call record with function fn and no argument yet *)
Lemma rcb_acall_new : forall bl rd a fn,
  0 <= fn < REC_FN_COUNT -> aval_mem rd (a + CALL_OFF_FN) 4 fn -> aval_mem rd (a + CALL_OFF_NARGS) 4 0 ->
  acall_at bl rd a (fn, []) [].
Proof.
  intros bl rd a fn Hfn BF BA. unfold acall_at. cbn [fst snd length].
  split; [exact Hfn|]. split; [lia|]. split; [reflexivity|].
  split; [exact BF|]. split; [exact BA|]. split; [cbn [map]; constructor|].
  intros k s pn Es. destruct k; discriminate.
Qed.

(* the representation's parts outside the call table and the spill, with g_rec.ncalls free to change: the bytes
   [g_rec, g_rec + 8) and [g_rec + 912, g_rec + 960) and the answer and reply blocks are kept *)
Lemma rcb_arep_rest : forall bl bl' rd rd' R R' Q Q',
  arep_at bl rd A_G_REC A_REC_SPILL R Q ->
  r_answer R' = r_answer R -> r_reply R' = r_reply R -> r_refuse R' = r_refuse R -> r_code R' = r_code R ->
  r_nreplies R' = r_nreplies R -> r_state R' = r_state R -> r_host R' = r_host R ->
  l_answer Q' = l_answer Q -> l_reply Q' = l_reply Q ->
  rd_agree rd rd' A_G_REC 8 -> rd_agree rd rd' (A_G_REC + OFF_ANSWER) (REC_SIZE - OFF_ANSWER) ->
  (forall pn, In pn (oblk (l_answer Q) ++ oblk (l_reply Q)) -> In pn bl' /\ rd_agree rd rd' (fst pn) (snd pn)) ->
  ag1_calls bl' rd' A_G_REC A_REC_SPILL R' Q' ->
  ag1_own A_G_REC A_REC_SPILL Q' ->
  arep_at bl' rd' A_G_REC A_REC_SPILL R' Q'.
Proof.
intros bl bl' rd rd' R R' Q Q' (Hg8 & Hs8 & Hap & _ & HA & HR & HSC & _) E1 E2 E3 E4 E5 E6 E7 F1 F2 Hlo Hhi Hblk HC' HO'.
unfold arep_at. split; [exact Hg8|]. split; [exact Hs8|]. split; [exact Hap|]. split; [exact HC'|].
split.
{ rewrite E1, F1. unfold aanswer_at in *.
  destruct (r_answer R) as [x|], (l_answer Q) as [pn|] eqn:EA; try contradiction.
  - destruct HA as (V & Hnz & Hin & Hlen & Hstr & Hlx).
    destruct (Hblk pn) as [Hin' Hgp]; [apply in_or_app; left; cbn [oblk In]; left; reflexivity|].
    split; [apply (aval_mem_agree_in rd rd' (A_G_REC + OFF_ANSWER) (REC_SIZE - OFF_ANSWER));
      [exact V | exact Hhi | lia | unfold REC_SIZE, OFF_ANSWER; cbn; lia]|].
    split; [exact Hnz|]. split; [exact Hin'|]. split; [exact Hlen|]. split; [|exact Hlx].
    apply (astr_atR_agree_in rd rd' (fst pn) (snd pn)); [exact Hstr | exact Hgp | lia | lia].
  - apply (aval_mem_agree_in rd rd' (A_G_REC + OFF_ANSWER) (REC_SIZE - OFF_ANSWER));
      [exact HA | exact Hhi | lia | unfold REC_SIZE, OFF_ANSWER; cbn; lia]. }
split.
{ rewrite E2, F2. unfold areply_at in *.
  destruct (r_reply R) as [x|], (l_reply Q) as [pr|] eqn:ER; try contradiction.
  - destruct HR as (V1 & V2 & Hnz & Hne & Hin & Hl & Hb & Hlx).
    destruct (Hblk pr) as [Hin' Hgp]; [apply in_or_app; right; cbn [oblk In]; left; reflexivity|].
    split; [apply (aval_mem_agree_in rd rd' (A_G_REC + OFF_ANSWER) (REC_SIZE - OFF_ANSWER));
      [exact V1 | exact Hhi | unfold OFF_REPLY, OFF_ANSWER; lia | unfold REC_SIZE, OFF_ANSWER, OFF_REPLY; cbn; lia]|].
    split; [apply (aval_mem_agree_in rd rd' (A_G_REC + OFF_ANSWER) (REC_SIZE - OFF_ANSWER));
      [exact V2 | exact Hhi | unfold OFF_REPLY_SIZE, OFF_ANSWER; lia | unfold REC_SIZE, OFF_ANSWER, OFF_REPLY_SIZE; cbn; lia]|].
    split; [exact Hnz|]. split; [exact Hne|]. split; [exact Hin'|]. split; [exact Hl|]. split; [|exact Hlx].
    apply (abytes_atR_agree_in rd rd' (fst pr) (snd pr)); [exact Hb | exact Hgp | lia | lia].
  - destruct HR as [V1 V2].
    split; [apply (aval_mem_agree_in rd rd' (A_G_REC + OFF_ANSWER) (REC_SIZE - OFF_ANSWER));
      [exact V1 | exact Hhi | unfold OFF_REPLY, OFF_ANSWER; lia | unfold REC_SIZE, OFF_ANSWER, OFF_REPLY; cbn; lia]|].
    apply (aval_mem_agree_in rd rd' (A_G_REC + OFF_ANSWER) (REC_SIZE - OFF_ANSWER));
      [exact V2 | exact Hhi | unfold OFF_REPLY_SIZE, OFF_ANSWER; lia | unfold REC_SIZE, OFF_ANSWER, OFF_REPLY_SIZE; cbn; lia]. }
split; [|exact HO'].
destruct HSC as (Vr & Vc & Vn & Vs & Vh & Rg). unfold ag1_scalars. rewrite E3, E4, E5, E6, E7.
split; [apply (aval_mem_agree_in rd rd' A_G_REC 8); [exact Vr | exact Hlo | unfold OFF_REFUSE; lia | unfold OFF_REFUSE; cbn; lia]|].
split; [apply (aval_mem_agree_in rd rd' A_G_REC 8); [exact Vc | exact Hlo | unfold OFF_CODE; lia | unfold OFF_CODE; cbn; lia]|].
split; [apply (aval_mem_agree_in rd rd' (A_G_REC + OFF_ANSWER) (REC_SIZE - OFF_ANSWER));
  [exact Vn | exact Hhi | unfold OFF_NREPLIES, OFF_ANSWER; lia | unfold REC_SIZE, OFF_ANSWER, OFF_NREPLIES; cbn; lia]|].
split; [apply (aval_mem_agree_in rd rd' (A_G_REC + OFF_ANSWER) (REC_SIZE - OFF_ANSWER));
  [exact Vs | exact Hhi | unfold OFF_STATE, OFF_ANSWER; lia | unfold REC_SIZE, OFF_ANSWER, OFF_STATE; cbn; lia]|].
split; [apply (aval_mem_agree_in rd rd' (A_G_REC + OFF_ANSWER) (REC_SIZE - OFF_ANSWER));
  [exact Vh | exact Hhi | unfold OFF_HOST, OFF_ANSWER; lia | unfold REC_SIZE, OFF_ANSWER, OFF_HOST; cbn; lia]|].
exact Rg.
Qed.

Section r. Variable B : asyms.

(* record(fn) on the table arm: ncalls := n + 1, and the slot's fn and nargs fields written *)
Lemma rcb_rep_record_lt : forall ly S rd ly' S' rd' R O fn,
  rec_repA B ly S rd R O -> (length (r_calls R) < 16)%nat -> 0 <= fn < REC_FN_COUNT ->
  aval_mem rd' (A_G_REC + OFF_NCALLS) 4 (Z.of_nat (length (r_calls R)) + 1) ->
  aval_mem rd' (rec_slot R + CALL_OFF_FN) 4 fn -> aval_mem rd' (rec_slot R + CALL_OFF_NARGS) 4 0 ->
  (forall a, rcb_in_rec a -> ~ (A_G_REC + OFF_NCALLS <= a < A_G_REC + OFF_NCALLS + 4) ->
     ~ (rec_slot R <= a < rec_slot R + 8) -> rd' a = rd a) ->
  (forall pn, In pn O -> In pn (ablocks B ly' S') /\ rd_agree rd rd' (fst pn) (snd pn)) ->
  rec_repA B ly' S' rd' (rec_record R fn []) O.
Proof.
  intros ly S rd ly' S' rd' R O fn (Q & HR & HO) Hn Hfn BN BF BA KG KO.
  assert (Ec : rec_slot R = A_G_REC + OFF_CALLS + CALL_SIZE * Z.of_nat (length (r_calls R))).
  { unfold rec_slot. replace (Nat.ltb (length (r_calls R)) 16) with true by (symmetry; apply Nat.ltb_lt; exact Hn).
    reflexivity. }
  rewrite Ec in BF, BA, KG.
  rewrite (rec_record_calls R fn [] Hn).
  assert (KQ : forall pn, In pn (lay_blocks Q) -> In pn (ablocks B ly' S') /\ rd_agree rd rd' (fst pn) (snd pn))
    by (intros pn Hpn; apply KO; apply HO; exact Hpn).
  assert (LB : lay_blocks (RLay (l_calls Q ++ [[]]) (l_spill Q) (l_answer Q) (l_reply Q)) = lay_blocks Q).
  { unfold lay_blocks. cbn [l_calls l_spill l_answer l_reply]. rewrite concat_app. cbn [concat].
    rewrite !app_nil_r. reflexivity. }
  exists (RLay (l_calls Q ++ [[]]) (l_spill Q) (l_answer Q) (l_reply Q)). split; [|rewrite LB; exact HO].
  pose proof HR as (_ & _ & H3 & HC & _ & _ & _ & HW).
  destruct HC as (C1 & C2 & C3 & C4 & C5 & C6).
  unfold iv_apart, REC_SIZE, SC_SIZE in H3.
  apply (rcb_arep_rest _ _ rd rd' R _ Q _ HR); try reflexivity.
  - apply rd_agree_of. intros a Ha. apply KG; unfold rcb_in_rec, REC_SIZE, OFF_NCALLS, OFF_CALLS, CALL_SIZE in *; lia.
  - apply rd_agree_of. intros a Ha. apply KG; unfold rcb_in_rec, REC_SIZE, OFF_NCALLS, OFF_CALLS, OFF_ANSWER, CALL_SIZE in *; lia.
  - intros pn Hpn. apply KQ. unfold lay_blocks. apply in_or_app. right. apply in_or_app. right. exact Hpn.
  - unfold ag1_calls. cbn [set_calls r_calls r_spill l_calls l_spill].
    refine (conj _ (conj _ (conj _ (conj _ (conj _ C6))))).
    + rewrite length_app. cbn [length]. lia.
    + rewrite !length_app, C2. reflexivity.
    + rewrite length_app, Nat2Z.inj_add. exact BN.
    + intros i cl P Ecl EP.
      destruct (Nat.lt_ge_cases i (length (r_calls R))) as [Hi|Hi].
      * rewrite nth_error_app1 in Ecl by exact Hi. rewrite nth_error_app1 in EP by (rewrite C2; exact Hi).
        destruct (C4 i cl P Ecl EP) as [Hcl HL]. split; [|exact HL].
        apply (acall_at_agree _ _ rd rd' _ cl P Hcl).
        -- apply rd_agree_of. intros x Hx. apply KG; unfold rcb_in_rec, REC_SIZE, OFF_NCALLS, OFF_CALLS, CALL_SIZE in *; lia.
        -- intros pn Hpn. apply KQ. unfold lay_blocks. apply in_or_app. left. apply in_concat.
           exists P. split; [eapply nth_error_In; exact EP | exact Hpn].
      * destruct (Nat.eq_dec i (length (r_calls R))) as [->|Hne].
        -- rewrite nth_error_app2, Nat.sub_diag in Ecl by lia. cbn in Ecl. injection Ecl as <-.
           rewrite nth_error_app2 in EP by (rewrite C2; lia). rewrite C2, Nat.sub_diag in EP. cbn in EP.
           injection EP as <-.
           split; [exact (rcb_acall_new _ rd' _ fn Hfn BF BA) | constructor].
        -- exfalso. assert (N : nth_error (r_calls R ++ [(fn, [])]) i = None)
             by (apply nth_error_None; rewrite length_app; cbn [length]; lia).
           rewrite N in Ecl. discriminate.
    + apply (acall_at_agree _ _ rd rd' _ _ _ C5).
      * apply rd_agree_of. intros x Hx. apply KG; unfold rcb_in_rec, REC_SIZE, SC_SIZE, OFF_NCALLS, OFF_CALLS, CALL_SIZE in *; lia.
      * intros pn Hpn. apply KQ. unfold lay_blocks. apply in_or_app. right. apply in_or_app. left. exact Hpn.
  - unfold ag1_own. rewrite LB. exact HW.
Qed.

(* record(fn) on the spill arm, after rec_calls_free emptied the spill: its fn and nargs written; g_rec is kept, so
   RecBridge.v's arep_at_other carries the representation's other parts *)
Lemma rcb_rep_spill_fn : forall ly S rd ly' S' rd' R O fn,
  rec_repA B ly S rd R O -> snd (r_spill R) = [] -> 0 <= fn < REC_FN_COUNT ->
  aval_mem rd' (A_REC_SPILL + CALL_OFF_FN) 4 fn -> aval_mem rd' (A_REC_SPILL + CALL_OFF_NARGS) 4 0 ->
  (forall a, rcb_in_rec a -> ~ (A_REC_SPILL <= a < A_REC_SPILL + 8) -> rd' a = rd a) ->
  (forall pn, In pn O -> In pn (ablocks B ly' S') /\ rd_agree rd rd' (fst pn) (snd pn)) ->
  rec_repA B ly' S' rd' (set_spill R (fn, [])) O.
Proof.
  intros ly S rd ly' S' rd' R O fn (Q & HR & HO) Hs0 Hfn BF BA KG KO.
  assert (KQ : forall pn, In pn (lay_blocks Q) -> In pn (ablocks B ly' S') /\ rd_agree rd rd' (fst pn) (snd pn))
    by (intros pn Hpn; apply KO; apply HO; exact Hpn).
  exists Q. split; [|exact HO].
  pose proof HR as (_ & _ & H3 & HC & _ & _ & _ & HW).
  destruct HC as (C1 & C2 & C3 & C4 & C5 & C6).
  unfold iv_apart, REC_SIZE, SC_SIZE in H3.
  assert (Els : l_spill Q = []).
  { destruct C5 as (_ & _ & Hl & _). rewrite Hs0 in Hl. apply length_zero_iff_nil. exact Hl. }
  apply (arep_at_other _ _ rd rd' R _ Q Q HR); try reflexivity.
  - apply rd_agree_of. intros a Ha. apply KG; unfold rcb_in_rec, REC_SIZE, SC_SIZE, OFF_CALLS in *; lia.
  - apply rd_agree_of. intros a Ha. apply KG; unfold rcb_in_rec, REC_SIZE, SC_SIZE, OFF_ANSWER in *; lia.
  - intros pn Hpn. apply KQ. unfold lay_blocks. apply in_or_app. right. apply in_or_app. right. exact Hpn.
  - unfold ag1_calls. cbn [set_spill r_calls r_spill fst snd].
    refine (conj C1 (conj C2 (conj _ (conj _ (conj _ (Forall_nil _)))))).
    + apply (aval_mem_agree_in rd rd' A_G_REC REC_SIZE); [exact C3 | | unfold OFF_NCALLS; lia | unfold OFF_NCALLS, REC_SIZE; cbn; lia].
      apply rd_agree_of. intros x Hx. apply KG; unfold rcb_in_rec, REC_SIZE, SC_SIZE in *; lia.
    + intros i cl P Ecl EP. destruct (C4 i cl P Ecl EP) as [Hcl HL]. split; [|exact HL].
      assert (Hi : (i < length (r_calls R))%nat) by (apply nth_error_Some; rewrite Ecl; discriminate).
      apply (acall_at_agree _ _ rd rd' _ cl P Hcl).
      * apply rd_agree_of. intros x Hx. apply KG; unfold rcb_in_rec, REC_SIZE, SC_SIZE, OFF_CALLS, CALL_SIZE in *; lia.
      * intros pn Hpn. apply KQ. unfold lay_blocks. apply in_or_app. left. apply in_concat.
        exists P. split; [eapply nth_error_In; exact EP | exact Hpn].
    + rewrite Els. exact (rcb_acall_new _ rd' _ fn Hfn BF BA).
  - exact HW.
Qed.

(* the call count, in the form record()'s branch asks it *)
Lemma rcb_rep_ncalls : forall ly S rd R O, rec_repA B ly S rd R O ->
  (length (r_calls R) <= 16)%nat /\ aval_mem rd (A_G_REC + OFF_NCALLS) 4 (Z.of_nat (length (r_calls R))).
Proof. intros ly S rd R O (Q & (_ & _ & _ & (C1 & _ & C3 & _) & _) & _). split; assumption. Qed.

(* every block the recorder owns is a live block, apart from g_rec and record.spill *)
Lemma rcb_rep_blocks : forall ly S rd R O, rec_repA B ly S rd R O -> forall pn, In pn O ->
  In pn (ablocks B ly S) /\ iv_apart (fst pn) (snd pn) A_G_REC REC_SIZE /\ iv_apart (fst pn) (snd pn) A_REC_SPILL SC_SIZE.
Proof.
  intros ly S rd R O (Q & HR & HO) pn Hpn. apply HO in Hpn.
  split; [exact (lay_blocks_in _ _ _ _ _ _ HR pn Hpn)|].
  pose proof HR as (_ & _ & _ & _ & _ & _ & _ & (_ & HAP)). exact (HAP pn Hpn).
Qed.
End r.

(* the representation survives any change outside g_rec, record.spill and the recorder's blocks *)
Lemma rcb_arep_keep : forall bl bl' rd rd' R Q,
  arep_at bl rd A_G_REC A_REC_SPILL R Q ->
  (forall a, rcb_in_rec a -> rd' a = rd a) ->
  (forall pn, In pn (lay_blocks Q) -> In pn bl' /\ rd_agree rd rd' (fst pn) (snd pn)) ->
  arep_at bl' rd' A_G_REC A_REC_SPILL R Q.
Proof.
  intros bl bl' rd rd' R Q HR K KQ.
  pose proof HR as (_ & _ & _ & HC & _ & _ & _ & HW).
  apply (rcb_arep_rest bl bl' rd rd' R R Q Q HR); try reflexivity.
  - apply rd_agree_of. intros a Ha. apply K. unfold rcb_in_rec, REC_SIZE. lia.
  - apply rd_agree_of. intros a Ha. apply K. unfold rcb_in_rec, REC_SIZE, OFF_ANSWER in *. lia.
  - intros pn Hpn. apply KQ. unfold lay_blocks. apply in_or_app. right. apply in_or_app. right. exact Hpn.
  - destruct HC as (C1 & C2 & C3 & C4 & C5 & C6).
    refine (conj C1 (conj C2 (conj _ (conj _ (conj _ C6))))).
    + apply (aval_mem_agree_in rd rd' A_G_REC REC_SIZE); [exact C3 | | unfold OFF_NCALLS; lia | unfold OFF_NCALLS, REC_SIZE; cbn; lia].
      apply rd_agree_of. intros x Hx. apply K. unfold rcb_in_rec. lia.
    + intros i c P Ec EP. destruct (C4 i c P Ec EP) as [Hc HL]. split; [|exact HL].
      assert (Hi : (i < length (r_calls R))%nat) by (apply nth_error_Some; rewrite Ec; discriminate).
      apply (acall_at_agree bl bl' rd rd' _ c P Hc).
      * apply rd_agree_of. intros x Hx. apply K. unfold rcb_in_rec, OFF_CALLS, CALL_SIZE, REC_SIZE in *. lia.
      * intros pn Hpn. apply KQ. unfold lay_blocks. apply in_or_app. left. apply in_concat.
        exists P. split; [eapply nth_error_In; exact EP | exact Hpn].
    + apply (acall_at_agree bl bl' rd rd' _ _ _ C5).
      * apply rd_agree_of. intros x Hx. apply K. unfold rcb_in_rec, CALL_SIZE, SC_SIZE in *. lia.
      * intros pn Hpn. apply KQ. unfold lay_blocks. apply in_or_app. right. apply in_or_app. left. exact Hpn.
  - exact HW.
Qed.

Lemma rcb_nodup_app : forall {X} (l l' : list X) a, List.NoDup (l ++ l') -> In a l -> In a l' -> False.
Proof.
intros X. induction l as [|x l IH]; intros l' a Hnd Hin Hin'; [destruct Hin|].
cbn [app] in Hnd. inversion Hnd as [|y k Hni Hnd' Hyk]. subst.
destruct Hin as [<- | Hin]; [apply Hni; apply in_or_app; right; exact Hin' | exact (IH l' a Hnd' Hin Hin')].
Qed.

(* the recorder's blocks other than the spill's: those of its blocks the spill does not hold *)
Lemma rcb_spill_split : forall Q pn, NoDup (map fst (lay_blocks Q)) ->
  (In pn (concat (l_calls Q) ++ oblk (l_answer Q) ++ oblk (l_reply Q)) <->
   In pn (lay_blocks Q) /\ ~ In pn (l_spill Q)).
Proof.
intros Q pn HND. apply NoDup_ListNoDup in HND. unfold lay_blocks in *. rewrite !map_app in HND. split.
- intros H. apply in_app_or in H as [H | H].
  + split; [apply in_or_app; left; exact H|]. intros Hs.
    exact (rcb_nodup_app _ _ (fst pn) HND (in_map fst _ _ H) (in_or_app _ _ _ (or_introl (in_map fst _ _ Hs)))).
  + split; [apply in_or_app; right; apply in_or_app; right; exact H|]. intros Hs.
    apply (List.NoDup_app_remove_l _ _) in HND. rewrite <- map_app in HND.
    exact (rcb_nodup_app _ _ (fst pn) HND (in_map fst _ _ Hs) (in_map fst _ _ H)).
- intros [H Hn]. apply in_app_or in H as [H | H]; [apply in_or_app; left; exact H|].
  apply in_app_or in H as [H | H]; [contradiction | apply in_or_app; right; exact H].
Qed.
