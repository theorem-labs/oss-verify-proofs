(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: the program walk of rec_calls_equal on the ASan+UBSan build of plugin-hostd/fuzz_command
   (0x89ef8, 164 instructions, frame 144 bytes), ported from the ASan walk lib/A/Prog/rec_calls_equal.v (0x89968). The
   shape is the A walk's: the symbolic executor over the position-abstract listing (CmdPaLib.v), the inline checks removed
   by the shadow tokens (PaShadow.v), the strcmp wrapper's call stepped through by its Theorem Labs lane contract (PaArt.v
   aj_art_at), the two loops cut at their heads (0x89f98, 0x8a064) and at the outer latch (0x8a0b4), each piece re-seeded
   from the concrete state there, the loops proved by induction. What B changes:
   - the frame (144 bytes) keeps n at 0(sp), the UBSan predicates `b mod 8 = 0 && b <> 0`, `b <> 0`,
     `a mod 8 = 0 && a <> 0` at 8(sp), 16(sp), 24(sp), and b at 32(sp); a stays in a5/s11 and `a <> 0` in a4/s8;
   - the inner loop counts s5 = 8k up to s2 = 8 * nargs and forms both argument addresses from s3/s10 (a[i].args) and
     s1/s9 (b[i].args) plus s5 (the seed's alias facts name the two sums);
   - eight UBSan trap branches, all to the `unimp` at 0x8a168, are refuted from the run's facts: 0x89fac, 0x89fbc,
     0x89fe4, 0x89ff4 are decided by the executor (a4 = 1 and the three predicate slots = 1 at the outer seed, which the
     entry derives from rce_calls' `a mod 8 = 0` and rce_home's 4096 <= a; a + 56i >= 4096 by the seed's atom fact);
     0x89fb4 and 0x89fec (a + 56i < a, b + 56i < b unsigned) and 0x8a064, 0x8a068 (~(a[i].args) < 8k, ~(b[i].args) < 8k)
     are refuted at the branch from the values of their operands. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_command/lib/B/Prog/rec_calls_equal.v, with its module paths, module names and numbers changed; 1569 of its 1744 lines of code are new or changed and 1417 lines of the source are left out. *)
(* reac_declared_vlan_add on fuzz_segconf.asan (image A, entry BASE + AF_reac_declared_vlan_add = 0x89e4c, 123
   instructions, 112-byte frame, no side-stack frame): the walk of lib/A/Prog/reac_declared_vlan_add_c.v
   (reac_declared_vlan_add_walk). Written for the walk lane of the G4 / G5 walk owner, in the form of plugin-hostd/fuzz_command's
   released lib/A/Prog walks (rec_calls_equal.v: the symbolic executor over the position-abstract listing, the inline
   checks removed by the shadow tokens, the loop cut at its head and re-seeded there; socket_send.v: the checked
   memset by aj_intrin_atS; PaArtOwn.aj_art_own_at: a wrapper that writes footprint bytes).
   Cuts (listing offsets from BASE): the loop head 0x51a4 (0x89ed8), the latch 0x51cc (0x89f00), after the search
   0x51f4 (0x89f28), the store 0x524c (0x89f80), the epilogue 0x5278 (0x89fac).
   Stretches: the entry 0x89e4c .. 0x89ed8 / 0x89f28 (frame, three nonzero tests, the shadow base, inline check 1 on
   the count cell, the count, blez: vad_entry); the search body with inline check 2 and the strcmp call at 0x89ef8
   (vad_step); the latch (vad_latch); the full test, the checked memset at 0x89f40, inline check 3, the strncpy call
   at 0x89f60, inline check 4 (vad_aft); the store stretch with inline check 5, the vid store and the count store
   (vad_store); the epilogue (vad_epi, vad_keep). The step plan: provenance/evidence/listing-plans/plan-reac_declared_vlan_add.md.
   Section hypotheses: TL (the listing's record of the shadow-base cell), ASTRCMP (interface row 17), ASTRNCPY
   (row 12), AMEMSET (the kit's aintrin_realizes OSet); STK_reac_declared_vlan_add and RLO_A / RHI_A are SegInstA's. *)
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP00 YP0i YCbn.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import PaTable PaSym.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YN3v YI04 YG0s.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import PaStep.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YI16 YG0p YC5d YG0q.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import PaRun PaShadow PaJournal SegSyms SegList SegPa SegPaLib.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import PaDenot PaSB PaLibG PaLibH PaLibF PaCallRun PaCall.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Spec Require Import SegModel.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog Require seg_spec.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Lib Require Mem.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import SegPgBase SegABase reac_declared_vlan_add_c.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import reac_declared_vlan_add_lem.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Rt Require Import RtDefs.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import PaArt.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Spec Require SegBridge.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Rt Require RtString RtSeg.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import PaArtOwn.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import SegInstA.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.

(* ---------- readers: carrying byte facts across a state that agrees outside a window ---------- *)
Definition vad_kept (rd rd' : reader) (lo hi : Z) : Prop :=
forall a, 0 <= a < 2 ^ 64 -> ~ (lo <= a < hi) -> rd' a = rd a.
Lemma vad_kept_trans : forall rd1 rd2 rd3 lo hi lo' hi',
vad_kept rd1 rd2 lo hi -> vad_kept rd2 rd3 lo' hi' -> lo <= lo' -> hi' <= hi -> vad_kept rd1 rd3 lo hi.
Proof. intros rd1 rd2 rd3 lo hi lo' hi' H12 H23 Hl Hh a Ha Hn. rewrite (H23 a Ha) by lia. exact (H12 a Ha Hn). Qed.
Lemma vad_sa_bytes_keep : forall (rd rd' : reader) (P : Z -> Prop) a bs,
(forall x, P x -> rd' x = rd x) -> sa_bytes rd a bs ->
(forall i, (i < length bs)%nat -> P (a + Z.of_nat i)) -> sa_bytes rd' a bs.
Proof. intros rd rd' P a bs HK H HP i Hi. rewrite (HK _ (HP i Hi)). exact (H i Hi). Qed.
Lemma vad_sa_val_keep : forall (rd rd' : reader) (P : Z -> Prop) a k v,
(forall x, P x -> rd' x = rd x) -> sa_val rd a k v ->
(forall i, (i < k)%nat -> P (a + Z.of_nat i)) -> sa_val rd' a k v.
Proof. intros rd rd' P a k v HK H HP i Hi. rewrite (HK _ (HP i Hi)). exact (H i Hi). Qed.
Lemma vad_sa_rtab_keep : forall (rd rd' : reader) (P : Z -> Prop) a t,
(forall x, P x -> rd' x = rd x) -> sa_rtab rd a t ->
(forall i, (i < 18 * length t)%nat -> P (a + Z.of_nat i)) -> sa_rtab rd' a t.
Proof.
intros rd rd' P a t HK (bs & Hb & He) HP. exists bs. split; [|exact He].
apply (vad_sa_bytes_keep rd rd' P a bs HK Hb). intros i Hi. apply HP. destruct He as [HL _]. lia.
Qed.
Lemma vad_val_mem_of_sa : forall segs H mem a k v, sa_val (aview segs H mem) a k v -> val_mem segs (mrestrict H mem) a k v.
Proof.
intros segs H mem a k v Hr i Hi. pose proof (Hr i Hi) as Hb.
destruct (aview_byte segs H mem _ _ Hb) as (b & Hm & Hbv & Hrange). rewrite Hm. f_equal. apply bv_eq.
rewrite Z_to_bv_unsigned. unfold bv_wrap. rewrite <- Hbv. rewrite Z.mod_small; [reflexivity|].
change (bv_modulus 8) with 256. exact Hrange.
Qed.
Lemma vad_sa_of_val_mem : forall segs H m0 x k v, val_mem segs (mrestrict H m0) x k v -> sa_val (aview segs H m0) x k v.
Proof.
intros segs H m0 x k v Hv i Hi. unfold aview. rewrite (Hv i Hi). cbn [option_map]. f_equal.
rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 8) with 256. unfold le_byte. apply Z.mod_mod. lia.
Qed.

Lemma vad_set_fs_self : forall S0 : astate, S0 = set_fs (st_fs S0) S0.
Proof. intros []; reflexivity. Qed.

Section b. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section d.
Context {PI : PAImg seg_listing}.
#[local] Notation SEGS := (@pa_segs _ seg_listing PI).
#[local] Notation VAL := (@pa_val _ seg_listing PI).
#[local] Notation SIG s := (@pa_sigma _ seg_listing PI s).
#[local] Notation BASE := (@pa_val _ seg_listing PI A_TEXT).
#[local] Notation rdW W mem := (aview SEGS (w_H W) mem).

(* listing offsets from BASE (BASE + 0x5118 = 0x89e4c) *)
Definition VAD_LH : Z := 0x51a4.   (* 0x89ed8, the search loop's head *)
Definition VAD_LT : Z := 0x51cc.   (* 0x89f00, the search loop's latch *)
Definition VAD_AFT : Z := 0x51f4.  (* 0x89f28, bge s10, s5 *)
Definition VAD_ST : Z := 0x524c.   (* 0x89f80, a0 = &tab[count].vid *)
Definition VAD_EPI : Z := 0x5278.  (* 0x89fac, mv a0, s4 *)
Definition VAD_RCMP : Z := 0x51c8. (* 0x89efc, the strcmp call's return *)
Definition VAD_RMS : Z := 0x5210.  (* 0x89f44, the checked memset's return *)
Definition VAD_RSN : Z := 0x5230.  (* 0x89f64, the strncpy call's return *)
(* the frame: ra and s0 .. s11 at sp0 - 8 .. sp0 - 104 *)
Definition vad_saved : list Z := [1; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27].
Definition vad_spF : afact := mkAF (2 ^ 46) (2 ^ 47) 4.
Definition vad_SBF : afact := mkAF SB SB 0.
Definition vad_PTRF : afact := mkAF 4096 (2 ^ 47 - 64) 0.
Definition vad_Bx : sv := SOff 32 0.
Definition vad_shx (k : nat) : sv := SAlu ALU_ADD (SAlu ALU_SRL (SOff k 0) (SLit 3)) (SOff 32 0).

(* ---- the symbolic states of the cut points; atoms 32 .. are the seed's extra words ---- *)
Definition vad_estack : YP09.region := YP09.mkRegion (Some 2%nat) 0 112 0 0
  (map (fun j => YP09.mkChunk (104 - 8 * Z.of_nat j) (CVal 8 (SOff (32 + j) 0))) (seq 0 13)).
Definition vad_ss_epi : sstate := mkSS VAD_EPI sr_atoms [vad_estack] None (mkFacts [(2%nat, vad_spF)] [] []).
(* the entry: the frame window, the GOT word and the shadow-base cell, the count cell at a2 (atom 33 = its value) *)
Definition vad_nregion0 : YP09.region := YP09.mkRegion (Some 12%nat) 0 4 0 0 [YP09.mkChunk 0 (CVal 4 (SOff 33 0))].
Definition vad_ss_entry : sstate := mkSS AF_reac_declared_vlan_add sr_atoms
  [stack_region 112; got_regionP; bcell_regionP 32; vad_nregion0] None
  (mkFacts [(2%nat, vad_spF); (32%nat, vad_SBF); (12%nat, mkAF 4096 (2 ^ 47 - 4) 2); (33%nat, mkAF 0 (2 ^ 31 - 1) 0)] [] []).
Definition vad_entry_SH : list shent := [mkSHE 12 0 4].
(* the loop head at entry i: atom 32 = SB, 33 = tab + 18 i, 34 = tab[i].vid *)
Definition vad_lh_regs : list sv := sr_set (sr_set (sr_set sr_atoms 24 (SOff 32 0)) 23 (SOff 33 0)) 22 (SOff 33 16).
Definition vad_entryR : YP09.region := YP09.mkRegion (Some 33%nat) 0 18 0 0 [YP09.mkChunk 16 (CVal 2 (SOff 34 0))].
Definition vad_ss_lh : sstate := mkSS VAD_LH vad_lh_regs [vad_entryR] None
  (mkFacts [(2%nat, vad_spF); (32%nat, vad_SBF); (33%nat, vad_PTRF); (34%nat, mkAF 0 65535 0)] [] []).
Definition vad_lh_SH : list shent := [mkSHE 33 0 18].
(* the latch at entry i: atom 32 = SB, 33 = tab + 18 i, 34 = length t - i *)
Definition vad_lt_regs : list sv :=
  sr_set (sr_set (sr_set (sr_set sr_atoms 24 (SOff 32 0)) 23 (SOff 33 0)) 22 (SOff 33 16)) 27 (SOff 34 0).
Definition vad_ss_lt : sstate := mkSS VAD_LT vad_lt_regs [] None
  (mkFacts [(2%nat, vad_spF); (32%nat, vad_SBF); (33%nat, vad_PTRF); (34%nat, mkAF 1 (2 ^ 31 - 1) 0)] [] []).
(* after the search: atom 32 = SB, 33 = n, 34 = the count; the count cell's region (kept across the calls) *)
Definition vad_aft_regs : list sv :=
  sr_set (sr_set (sr_set (sr_set sr_atoms 24 (SOff 32 0)) 8 (SOff 33 0)) 25 (vad_shx 33)) 26 (SOff 34 0).
Definition vad_nregionA : YP09.region := YP09.mkRegion (Some 33%nat) 0 4 0 0 [YP09.mkChunk 0 (CVal 4 (SOff 34 0))].
Definition vad_ss_aft : sstate := mkSS VAD_AFT vad_aft_regs [vad_nregionA] None
  (mkFacts [(2%nat, vad_spF); (32%nat, vad_SBF); (33%nat, mkAF 4096 (2 ^ 47 - 4) 2); (34%nat, mkAF 0 (2 ^ 31 - 1) 0)] [] []).
Definition vad_aft_SH : list shent := [mkSHE 33 0 4].
(* the store: atom 32 = SB, 33 = n, 34 = the count, 35 = tab + 18 count; a0 = atom 35 + 16 *)
Definition vad_st_regs : list sv :=
  sr_set (sr_set (sr_set sr_atoms 24 (SOff 32 0)) 8 (SOff 33 0)) 10 (SOff 35 16).
Definition vad_nregionS : YP09.region := YP09.mkRegion (Some 33%nat) 0 4 0 4 [YP09.mkChunk 0 (CVal 4 (SOff 34 0))].
Definition vad_vidR : YP09.region := YP09.mkRegion (Some 35%nat) 0 18 16 18 [].
Definition vad_ss_st : sstate := mkSS VAD_ST vad_st_regs [vad_vidR; vad_nregionS] None
  (mkFacts [(2%nat, vad_spF); (32%nat, vad_SBF); (33%nat, mkAF 4096 (2 ^ 47 - 4) 2); (34%nat, mkAF 0 (2 ^ 31 - 2) 0);
            (35%nat, vad_PTRF)] [] []).
Definition vad_st_SH : list shent := [mkSHE 35 16 18; mkSHE 33 0 4].

Section e.
Variable B : asyms.
Hypothesis TL : PALib B.
Hypothesis ASTRCMP : forall fx0 : YK11.FPState, @RtString.astrcmp_realizes fx0 rc SEGS B (SIG SS___interceptor_trampoline_strcmp).
Hypothesis ASTRNCPY : forall fx0 : YK11.FPState, @RtSeg.astrncpy_realizes fx0 rc SEGS B (SIG SS___interceptor_trampoline_strncpy).
Hypothesis AMEMSET : forall fx0 : YK11.FPState, @aintrin_realizes fx0 rc SEGS B OSet (SIG SS___asan_memset).
Let LAWS : AR_laws SEGS B := AR_laws_ok SEGS B.
Let errno_low := pal_env B TL.
Let RUN := paj_run B LAWS. Let RUNTO := paj_run_to B LAWS.
Let BR := paj_branch (PI := PI).
Let RET := paj_ret_at (PL := PL_seg) (PI := PI).

Ltac vad_regs_ok EE eqs :=
  apply regs_ok_by_cases; intros rr Hrr; cbv [all_regs In] in Hrr;
  repeat (destruct Hrr as [<- | Hrr];
    [ lazymatch goal with |- getr _ _ = sv_denot _ (sr_get ?a0 ?rr2) =>
        let v := eval vm_compute in (sr_get a0 rr2) in change (sr_get a0 rr2) with v end;
      cbn [sv_denot];
      first [ reflexivity
            | rewrite Z.add_0_r, Z_to_bv_bv_unsigned; symmetry; apply EE; reflexivity
            | rewrite ?Z.add_0_r; eqs; assumption ]
    | ]); try (destruct Hrr).
Ltac vad_md :=
  lazymatch goal with HJ : ajournal _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ?md2 _ |- _ =>
    lazymatch md2 with with_vm_backing _ _ _ => let m := fresh "mdv" in set (m := md2) in *; clearbody m | _ => idtac end end.
Ltac vad_keep_empty HFr K :=
  lazymatch type of HFr with frame_of _ _ (mrestrict ?H ?m1) (mrestrict ?H ?m2) =>
  assert (K : forall x, 0 <= x < 2 ^ 64 -> aview SEGS H m2 x = aview SEGS H m1 x)
  by (intros x0 Hx0; apply (kept_of_frame (segs := SEGS) _ _ _ _ _ (fun _ => False) HFr);
      [ intros b0 wlo whi a0 Hin Hrr; vm_compute in Hin;
        repeat (destruct Hin as [Hq | Hin]; [injection Hq as <- <- <-; cbn [base_val] in Hrr; lia|]); destruct Hin
      | exact Hx0 | tauto ]) end.
Ltac vad_keep_win HFr K lo hi Usp :=
  lazymatch type of HFr with frame_of _ _ (mrestrict ?H ?m1) (mrestrict ?H ?m2) =>
  assert (K : vad_kept (aview SEGS H m1) (aview SEGS H m2) lo hi)
  by (intros x0 Hx0 Hn0; apply (kept_of_frame (segs := SEGS) _ _ _ _ _ (fun x => lo <= x < hi) HFr);
      [ intros b0 wlo whi a0 Hin Hrr; vm_compute in Hin;
        repeat (destruct Hin as [Hq | Hin]; [injection Hq as <- <- <-; cbn [base_val ew ewset Nat.eqb] in Hrr; rewrite ?Usp in Hrr; lia|]); destruct Hin
      | exact Hx0 | exact Hn0 ]) end.

(* ---------- one call of reac_declared_vlan_add ---------- *)
Section w.
Variables (ly : alayout) (S : astate) (W : world SEGS) (regs : bvmap 5 word) (mem : word -> option byte) (md : Model)
  (ch : list (Z * Z * Z)) (rlo rhi tab max n par vid : Z) (t : list (list Z * Z)) (p : list Z).
Hypothesis HPRE : afn_pre SEGS B STK_reac_declared_vlan_add ly S W regs mem md ch.
Hypothesis HROD : arodata_okP SEGS rlo rhi B (rdW W mem).
Hypothesis H10 : getr regs 10 = w64 tab.
Hypothesis H11 : getr regs 11 = w64 max.
Hypothesis H12 : getr regs 12 = w64 n.
Hypothesis H13 : getr regs 13 = w64 par.
Hypothesis H14 : getr regs 14 = w64 vid.
Hypothesis HADD : add_pre SEGS B ly S W mem regs tab max n par vid t p.
Collection vad_all := TL HPRE HROD H10 H11 H12 H13 H14 HADD.
Collection vad_allc := vad_all ASTRCMP.
Collection vad_allm := vad_all AMEMSET ASTRNCPY.

#[local] Notation L := (Z.of_nat (length t)).
#[local] Notation VA := (vlan_add t max p vid).
#[local] Notation sp0 := (spZ regs).
Definition vad_FP : list (Z * Z) := vtab_W tab n t (snd (vlan_add t max p vid)).

Definition vad_Q : world SEGS -> config -> Prop :=
apost_base SEGS B STK_reac_declared_vlan_add vad_FP regs ly S W mem md 0
(fun ly' S' W' regs' mem' md' =>
 getr regs' 10 = w64 (fst VA) /\
 sa_rtab (rdW W' mem') tab (snd VA) /\
 sa_val (rdW W' mem') n 4 (Z.of_nat (length (snd VA))) /\
 (sa_guardtab (rdW W mem) tab max -> sa_guardtab (rdW W' mem') tab max) /\
 sa_kept SEGS W mem W' mem' regs STK_reac_declared_vlan_add (vtab_E tab n t (snd VA)) /\
 sa_noalloc B ly S ly' S').

(* the saved registers in the frame *)
Definition vad_frame (rd : reader) : Prop :=
forall j r, nth_error vad_saved j = Some r ->
sa_val rd (sp0 - 8 - 8 * Z.of_nat j) 8 (bv_unsigned (getr regs (Z_to_bv 5 r))).
(* a point after the prologue: the journal from the entry, the frame, sp, gp, tp *)
Definition vad_cutE (regs1 : bvmap 5 word) (mem1 : word -> option byte) (md1 : Model) : Prop :=
ajournal SEGS B STK_reac_declared_vlan_add sp0 vad_FP ly S W mem md [] ly S W mem1 md1 0 /\
vad_frame (rdW W mem1) /\
getr regs1 2 = w64 (sp0 - 112) /\ getr regs1 3 = getr regs 3 /\ getr regs1 4 = getr regs 4.
(* a point before the append: also the memory below and above the stack window unchanged *)
Definition vad_cut (regs1 : bvmap 5 word) (mem1 : word -> option byte) (md1 : Model) : Prop :=
vad_cutE regs1 mem1 md1 /\ vad_kept (rdW W mem) (rdW W mem1) (sp0 - STK_reac_declared_vlan_add) sp0.
(* the registers every cut after the entry stretch carries *)
Definition vad_regs (regs1 : bvmap 5 word) : Prop :=
getr regs1 8 = w64 n /\ getr regs1 9 = w64 vid /\ getr regs1 18 = w64 tab /\ getr regs1 19 = w64 par /\
getr regs1 20 = w64 (-1) /\ getr regs1 21 = w64 max /\ getr regs1 24 = w64 SB /\
getr regs1 25 = w64 (SB + n / 8) /\ getr regs1 26 = w64 L.
(* the search loop's head, entry i; entries 0 .. i - 1 did not match *)
Definition vad_LHc (i : nat) (regs1 : bvmap 5 word) (mem1 : word -> option byte) (md1 : Model) : Prop :=
vad_cut regs1 mem1 md1 /\ vad_regs regs1 /\ (i < length t)%nat /\
existsb (vad_match vid p) t = existsb (vad_match vid p) (skipn i t) /\
getr regs1 23 = w64 (tab + 18 * Z.of_nat i) /\ getr regs1 22 = w64 (tab + 18 * Z.of_nat i + 16) /\
getr regs1 27 = w64 (L - Z.of_nat i).
(* the latch after entry i, which did not match *)
Definition vad_LTc (i : nat) (regs1 : bvmap 5 word) (mem1 : word -> option byte) (md1 : Model) : Prop :=
vad_cut regs1 mem1 md1 /\ vad_regs regs1 /\ (i < length t)%nat /\
existsb (vad_match vid p) t = existsb (vad_match vid p) (skipn (Datatypes.S i) t) /\
getr regs1 23 = w64 (tab + 18 * Z.of_nat i) /\ getr regs1 22 = w64 (tab + 18 * Z.of_nat i + 16) /\
getr regs1 27 = w64 (L - Z.of_nat i).
(* after the search: no entry matches *)
Definition vad_AFTc (regs1 : bvmap 5 word) (mem1 : word -> option byte) (md1 : Model) : Prop :=
vad_cut regs1 mem1 md1 /\ vad_regs regs1 /\ existsb (vad_match vid p) t = false.

(* ---------- the facts of the entry that every stretch uses ---------- *)
Lemma vad_sp : sp0 mod 16 = 0 /\ alloc_ceiling + STK_reac_declared_vlan_add <= sp0 /\ sp0 <= 2 ^ 47 /\ alloc_ceiling mod 4096 = 0.
Proof using vad_all.
pose proof HPRE as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof alloc_ceiling_value as [_ HAC]. repeat split; lia.
Qed.
Lemma vad_noalloc : sa_noalloc B ly S ly S.
Proof using. split; [apply Permutation_refl|]. split; [reflexivity|]. exists (st_fs S). apply vad_set_fs_self. Qed.
(* the table: a live block below the heap's ceiling, in application memory, present *)
Lemma vad_tab_facts :
4096 <= tab /\ tab + 18 * (max + 1) <= alloc_ceiling /\ Z.of_nat (length t) <= max < 2 ^ 31 /\ tab mod 16 = 0 /\
(forall x, tab <= x < tab + 18 * (max + 1) -> ~ (SB <= x < SB + 2 ^ 44)) /\
(forall x, tab <= x < tab + 18 * (max + 1) -> apresent (w_H W) mem x).
Proof using vad_all.
pose proof HPRE as (HAR & _).
destruct HADD as ((Htab0 & Htab16 & HRT & HLm & (b & m & Hbm & Hb1 & Hb2) & _) & _).
destruct (al_blocks _ _ LAWS ly S W mem md b m HAR Hbm) as (Hp16 & Hp4096 & Hpceil & Hpapp & Hppres & _ & Hkr).
pose proof (req_size_pos m ltac:(unfold seg_spec.RVLAN_SIZE in *; lia)) as [_ Hreq].
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5). unfold seg_spec.RVLAN_SIZE in *.
split; [lia|]. split; [lia|]. split; [exact HLm|]. split; [exact Htab16|]. split.
- intros x Hx. unfold in_app, kLowShadowBeg, kHighMemBeg, SB in *. lia.
- intros x Hx. exact (proj1 (Hppres x ltac:(lia))).
Qed.
(* the count cell: outside the stack window, in application memory *)
Lemma vad_n_facts :
4096 <= n /\ n + 4 <= 2 ^ 47 /\ n mod 4 = 0 /\ (n + 4 <= alloc_ceiling \/ sp0 <= n) /\
(forall x, n <= x < n + 4 -> ~ (SB <= x < SB + 2 ^ 44)) /\
(n + 4 <= tab \/ tab + 18 * (max + 1) <= n) /\ (n + 4 <= 0x10000 \/ 0x601000 <= n).
Proof using vad_all.
pose proof HPRE as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
destruct HADD as ((_ & _ & _ & _ & _ & _ & _ & Hn0 & Hn4 & _ & HDST & _ & HDJ) & _).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (LT : kHighMemBeg <= ly_stk_lo ly).
{ pose proof (lo_top _ (am_layout _ _ _ _ (proj1 HAR))) as (_ & _ & _ & _ & _ & _ & L3). exact L3. }
unfold sa_disj, seg_spec.RVLAN_SIZE in HDJ.
destruct HDST as [((cid & pos & Hin & Hcid & Hf1 & Hf2) & _) | [((b & m & Hbm & Hb1 & Hb2) & _) | (Hs1 & Hs2 & _)]].
- destruct (frames_bounds SEGS B LAWS ly S W mem md cid pos HAR Hin) as (Hf4 & Hfc & Hfa).
  pose proof (frm_off_imgP B ly S W mem md cid pos HAR Hin) as Hoi. unfold off_img in Hoi.
  unfold in_app, kLowShadowBeg, kHighMemBeg, SB in *.
  repeat split; try lia; intros x Hx; lia.
- destruct (al_blocks _ _ LAWS ly S W mem md b m HAR Hbm) as (Hp16 & Hp4096 & Hpceil & Hpapp & Hppres & _ & Hkr).
  pose proof (req_size_pos0 m ltac:(lia)) as [_ Hreq].
  pose proof (blk_off_imgP B ly S W mem md b m HAR Hbm) as Hoi. unfold off_img in Hoi.
  unfold in_app, kLowShadowBeg, kHighMemBeg, SB in *.
  repeat split; try lia; intros x Hx; lia.
- unfold kHighMemBeg, SB in *. repeat split; try lia; intros x Hx; lia.
Qed.

(* ---------- the epilogue: 0x89fac .. 0x89fe8, a0 = s4, ra and s0 .. s11 restored, ret ---------- *)
Definition vad_e_extra : list word := map (fun r => getr regs (Z_to_bv 5 r)) vad_saved.
Lemma vad_e_nth : forall j r, nth_error vad_saved j = Some r -> nth j vad_e_extra (Z_to_bv 64 0) = getr regs (Z_to_bv 5 r).
Proof using. intros j r H. unfold vad_e_extra. apply nth_error_nth. rewrite (map_nth_error (fun r0 => getr regs (Z_to_bv 5 r0)) j vad_saved H). reflexivity. Qed.
Lemma vad_epi_seed : forall regs1 mem1, getr regs1 2 = w64 (sp0 - 112) -> vad_frame (rdW W mem1) ->
st_ok_pi SEGS VAL (Eimg (Ereg regs1 vad_e_extra)) vad_ss_epi
  (restrict (w_H W) (mkst regs1 (Z_to_bv 64 (BASE + VAD_EPI)) mem1 (seg_rom SEGS)))
/\ sh_ok SEGS vad_Bx [] (Eimg (Ereg regs1 vad_e_extra)) (mrestrict (w_H W) mem1).
Proof using vad_all.
intros regs1 mem1 R2 HFR. pose proof vad_sp as (Hal16 & Hlo & Hhi & _).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5). assert (HST : STK_reac_declared_vlan_add = 8304) by reflexivity.
set (E := Eimg (Ereg regs1 vad_e_extra)).
assert (Usp : bv_unsigned (ew E 2) = sp0 - 112).
{ subst E. rewrite (ew_Eimg_Ereg_nat regs1 _ 2 2%bv eq_refl), R2. unfold w64. apply unsigned_lit_small. lia. }
split; [|apply Forall_nil].
rewrite restrict_mkst_fx. unfold vad_ss_epi. apply pa_entry_st_ok_full.
- subst E. apply regs_ok_Eimg_Ereg.
- vm_compute. reflexivity.
- apply Forall_cons; [|apply Forall_nil]. unfold region_ok, vad_estack.
  cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val]. rewrite Usp.
  split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
  apply Forall_forall. intros c Hc. apply in_map_iff in Hc as (j & <- & Hj). apply in_seq in Hj.
  destruct (nth_error vad_saved j) as [r|] eqn:Hr; [| apply nth_error_None in Hr; cbn in Hr; lia].
  pose proof (bv_unsigned_in_range 64 (getr regs (Z_to_bv 5 r))) as HRr. change (bv_modulus 64) with (2 ^ 64) in HRr.
  apply (chunk_ok_val SEGS E _ (sp0 - 112) (104 - 8 * Z.of_nat j) 8 (SOff (32 + j) 0) (bv_unsigned (getr regs (Z_to_bv 5 r)))).
  + cbn [sv_denot]. subst E. rewrite Eimg_low by (unfold A_TEXT; lia). rewrite ew_Ereg_extra, (vad_e_nth j r Hr).
    rewrite Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity.
  + change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64). exact HRr.
  + cbn. lia.
  + replace (sp0 - 112 + (104 - 8 * Z.of_nat j)) with (sp0 - 8 - 8 * Z.of_nat j) by lia.
    apply vad_val_mem_of_sa. exact (HFR j r Hr).
- cbn. tauto.
- split; [|split; exact I]. cbn [f_atoms atoms_ok]. split; [|exact I]. unfold afact_ok, vad_spF. cbn [af_lo af_hi af_al2]. rewrite Usp.
  change (2 ^ 4) with 16. split; [lia|]. split; [|lia]. rewrite Zminus_mod, Hal16. reflexivity.
Qed.
Lemma vad_epi : forall v regs1 mem1 md1, vad_cutE regs1 mem1 md1 -> getr regs1 20 = w64 v -> v = fst VA ->
sa_rtab (rdW W mem1) tab (snd VA) -> sa_val (rdW W mem1) n 4 (Z.of_nat (length (snd VA))) ->
(sa_guardtab (rdW W mem) tab max -> sa_guardtab (rdW W mem1) tab max) ->
(forall a, 0 <= a < 2 ^ 64 -> ~ (sp0 - STK_reac_declared_vlan_add <= a < sp0) -> ~ vtab_E tab n t (snd VA) a ->
  rdW W mem1 a = rdW W mem a) ->
SRr SEGS W (mkCfg (mkst regs1 (Z_to_bv 64 (BASE + VAD_EPI)) mem1 (seg_rom SEGS)) md1) vad_Q.
Proof using vad_all.
intros v regs1 mem1 md1 (HJ & HFR & R2 & R3 & R4) R20 Hv HT HN HGd HKE.
pose proof HPRE as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof vad_sp as (Hal16 & Hlo & Hhi & _).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5). assert (HST : STK_reac_declared_vlan_add = 8304) by reflexivity.
destruct (vad_epi_seed regs1 mem1 R2 HFR) as [HS SHOK].
assert (HEI : img_env VAL A_LIM (Eimg (Ereg regs1 vad_e_extra))) by apply Eimg_env.
assert (EE : forall k (r : bv 5), Z.of_nat k = bv_unsigned r -> ew (Eimg (Ereg regs1 vad_e_extra)) k = getr regs1 r)
  by (intros k r Hk; apply ew_Eimg_Ereg_nat; exact Hk).
assert (EX : forall j r, nth_error vad_saved j = Some r -> ew (Eimg (Ereg regs1 vad_e_extra)) (32 + j) = getr regs (Z_to_bv 5 r)).
{ intros j r Hr. assert (Hj : (j < 13)%nat) by (change 13%nat with (length vad_saved); apply (proj1 (nth_error_Some vad_saved j)); rewrite Hr; discriminate).
  rewrite Eimg_low by (unfold A_TEXT; lia). rewrite ew_Ereg_extra. exact (vad_e_nth j r Hr). }
assert (Usp : bv_unsigned (ew (Eimg (Ereg regs1 vad_e_extra)) 2) = sp0 - 112).
{ rewrite (EE 2%nat 2%bv eq_refl), R2. unfold w64. apply unsigned_lit_small. lia. }
pose proof (EX 0%nat 1 eq_refl) as E32. pose proof (EX 1%nat 8 eq_refl) as E33. pose proof (EX 2%nat 9 eq_refl) as E34.
pose proof (EX 3%nat 18 eq_refl) as E35. pose proof (EX 4%nat 19 eq_refl) as E36. pose proof (EX 5%nat 20 eq_refl) as E37.
pose proof (EX 6%nat 21 eq_refl) as E38. pose proof (EX 7%nat 22 eq_refl) as E39. pose proof (EX 8%nat 23 eq_refl) as E40.
pose proof (EX 9%nat 24 eq_refl) as E41. pose proof (EX 10%nat 25 eq_refl) as E42. pose proof (EX 11%nat 26 eq_refl) as E43.
pose proof (EX 12%nat 27 eq_refl) as E44.
cbn [Nat.add] in E32, E33, E34, E35, E36, E37, E38, E39, E40, E41, E42, E43, E44.
pose proof (EE 3%nat 3%bv eq_refl) as E3. pose proof (EE 4%nat 4%bv eq_refl) as E4. pose proof (EE 20%nat 20%bv eq_refl) as E20.
clear EX.
remember (Eimg (Ereg regs1 vad_e_extra)) as E eqn:HE. clear HE.
paj_run_tok RUN HS HJ SHOK Bspan.
{ awr_ok_tac; exact Usp. }
vad_md.
vad_keep_empty HFr KE.
prreg HS (1%bv : bv 5) F1. prreg HS (10%bv : bv 5) F10.
eapply (RET W _ _ _ _ _ HS eq_refl ltac:(vm_compute; reflexivity)).
intros mat'. unfold vad_Q, apost_base.
lazymatch goal with |- exists _ _ _ _ _, mkCfg (mkst ?r _ ?m _) ?d = _ /\ _ => exists ly, S, r, m, d end.
split.
{ rewrite F1, E32. change (getr regs (Z_to_bv 5 1)) with (getr regs 1). unfold YK0s.ret_ok in Hra. rewrite Hra. reflexivity. }
split.
{ apply (ajournal_materialize SEGS B LAWS pa_segs_low). exact HJ. }
split.
{ unfold aregs_preserved. intros r Hr.
  assert (Hcases : r = 2 \/ r = 3 \/ r = 4 \/ r = 8 \/ r = 9 \/ r = 18 \/ r = 19 \/ r = 20 \/ r = 21 \/ r = 22 \/ r = 23 \/
    r = 24 \/ r = 25 \/ r = 26 \/ r = 27) by (unfold acallee_saved in Hr; lia).
  clear Hr.
  repeat (destruct Hcases as [-> | Hcases]); [..| subst r];
  rewrite (st_ok_pi_restrict_reg (w_H W) E _ _ _ HS); cbn [ms_regs];
  lazymatch goal with |- sv_denot _ (sr_get ?a ?rr2) = _ => let v := eval vm_compute in (sr_get a rr2) in change (sr_get a rr2) with v end;
  cbn [sv_denot];
  first
  [ rewrite Usp; replace (sp0 - 112 + 112) with sp0 by lia; unfold spZ; rewrite Z_to_bv_bv_unsigned; reflexivity
  | rewrite Z.add_0_r, Z_to_bv_bv_unsigned;
    first [ rewrite E3, R3; reflexivity | rewrite E4, R4; reflexivity
          | rewrite E33; reflexivity | rewrite E34; reflexivity | rewrite E35; reflexivity | rewrite E36; reflexivity
          | rewrite E37; reflexivity | rewrite E38; reflexivity | rewrite E39; reflexivity | rewrite E40; reflexivity
          | rewrite E41; reflexivity | rewrite E42; reflexivity | rewrite E43; reflexivity | rewrite E44; reflexivity ] ]. }
split; [rewrite F10, E20, R20, Hv; reflexivity|].
split.
{ apply (vad_sa_rtab_keep _ _ (fun x => 0 <= x < 2 ^ 64) _ _ (fun x Hx => KE x Hx) HT).
  intros i Hi. pose proof vad_tab_facts as (T1 & T2 & T3 & _).
  pose proof (vad_vlan_add_len t max p vid (proj1 T3)) as [VL1 VL2]. lia. }
split.
{ apply (vad_sa_val_keep _ _ (fun x => 0 <= x < 2 ^ 64) _ _ _ (fun x Hx => KE x Hx) HN).
  intros i Hi. pose proof vad_n_facts as (N1 & N2 & _). lia. }
split.
{ intros HGg. apply (vad_sa_bytes_keep _ _ (fun x => 0 <= x < 2 ^ 64) _ _ (fun x Hx => KE x Hx) (HGd HGg)).
  intros i Hi. pose proof vad_tab_facts as (T1 & T2 & T3 & _). unfold seg_spec.GUARD_BYTES in Hi. rewrite repeat_length in Hi.
  cbv beta. unfold seg_spec.RVLAN_SIZE. lia. }
split; [intros a Ha Hw He; rewrite (KE a Ha); exact (HKE a Ha Hw He)|].
exact vad_noalloc.
Qed.

(* the exit with the table unchanged (a duplicate: 0; full: -1): the table, the count and the guard lie outside the
   stack window, which is all the memory the walk has changed *)
Lemma vad_keep : forall v regs1 mem1 md1, vlan_add t max p vid = (v, t) -> vad_cut regs1 mem1 md1 -> getr regs1 20 = w64 v ->
SRr SEGS W (mkCfg (mkst regs1 (Z_to_bv 64 (BASE + VAD_EPI)) mem1 (seg_rom SEGS)) md1) vad_Q.
Proof using vad_all.
intros v regs1 mem1 md1 EVA (HC & HK) R20.
pose proof vad_sp as (Hal16 & Hlo & Hhi & _).
pose proof vad_tab_facts as (T1 & T2 & T3 & _). pose proof vad_n_facts as (N1 & N2 & N3 & N4 & _).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5). assert (HST : STK_reac_declared_vlan_add = 8304) by reflexivity.
pose proof HADD as ((_ & _ & HRT & _ & _ & _ & _ & _ & _ & HNV & _) & _).
assert (HKP : forall x, (0 <= x < 2 ^ 64 /\ ~ (sp0 - STK_reac_declared_vlan_add <= x < sp0)) -> rdW W mem1 x = rdW W mem x)
  by (intros x [Hx1 Hx2]; exact (HK x Hx1 Hx2)).
apply (vad_epi v regs1 mem1 md1 HC R20); rewrite ?EVA; cbn [fst snd]; [reflexivity | | | |].
- apply (vad_sa_rtab_keep _ _ _ _ _ HKP HRT). intros i Hi. cbv beta. lia.
- apply (vad_sa_val_keep _ _ _ _ _ _ HKP HNV). intros i Hi. cbv beta. lia.
- intros HG. apply (vad_sa_bytes_keep _ _ _ _ _ HKP HG). intros i Hi. cbv beta.
  unfold seg_spec.GUARD_BYTES in Hi. rewrite repeat_length in Hi. unfold seg_spec.RVLAN_SIZE. lia.
- intros a Ha Hw _. exact (HK a Ha Hw).
Qed.

(* ---------- the shadow of a range a check reads, and the shadow index arithmetic ---------- *)
Lemma vad_shent_ok : forall E (H : word -> bool) mem' k x lo hi, ew E 32 = w64 SB -> bv_unsigned (ew E k) = x -> 0 <= x + lo -> x + hi < 2 ^ 64 -> lo <= hi ->
range_addressable (aview SEGS H mem') SHADOW_OFF (x + lo) (hi - lo) ->
(forall y, x + lo <= y < x + hi -> ~ (SB <= y < SB + 2 ^ 44)) ->
shent_ok SEGS vad_Bx E (mrestrict H mem') (mkSHE k lo hi).
Proof using.
intros E H mem' k x lo hi H32 Hk H0 H1 Hlh Hra Hband. unfold shent_ok, app_apart, vad_Bx. cbn [she_m she_lo she_hi].
assert (U32 : U E (SOff 32 0) = SB).
{ rewrite U_SOff, H32, Z.add_0_r. unfold w64. rewrite unsigned_lit_small by (unfold SB; lia). apply zcanon_small. unfold SB; lia. }
assert (Hxr : 0 <= x < 2 ^ 64) by (rewrite <- Hk; pose proof (bv_unsigned_in_range 64 (ew E k)) as HR; change (bv_modulus 64) with (2 ^ 64) in HR; exact HR).
assert (Uk : U E (SOff k 0) = x) by (rewrite U_SOff, Hk, Z.add_0_r; apply zcanon_small; exact Hxr).
rewrite U32, Uk. split; [exact Hra|].
intros y Hy. rewrite Z.min_l, Z.max_r in Hy by lia. apply Hband. lia.
Qed.
Lemma vad_srl3 : forall x, 0 <= x < 2 ^ 64 -> alu64 ALU_SRL (Z_to_bv 64 x) (Z_to_bv 64 3) = Z_to_bv 64 (x / 8).
Proof using.
intros x Hx. apply bv_eq. rewrite alu64_unsigned. cbn [zalu_raw]. rewrite !unsigned_lit_small by lia.
change (Z.land 3 63) with 3. rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 3) with 8.
assert (0 <= x / 8 < 2 ^ 64) by (split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]).
apply bv_wrap_small. change (bv_modulus 64) with (2 ^ 64). lia.
Qed.
Lemma vad_add64 : forall x y, 0 <= x -> 0 <= y -> x + y < 2 ^ 64 -> alu64 ALU_ADD (Z_to_bv 64 x) (Z_to_bv 64 y) = Z_to_bv 64 (x + y).
Proof using.
intros x y Hx Hy Hxy. apply bv_eq. rewrite alu64_unsigned. cbn [zalu_raw]. rewrite !unsigned_lit_small by lia.
apply bv_wrap_small. change (bv_modulus 64) with (2 ^ 64). lia.
Qed.
Lemma vad_shx_val : forall x, 0 <= x < 2 ^ 47 ->
alu64 ALU_ADD (alu64 ALU_SRL (Z_to_bv 64 x) (Z_to_bv 64 3)) (Z_to_bv 64 SB) = w64 (SB + x / 8).
Proof using.
intros x Hx. assert (0 <= x / 8 < 2 ^ 44) by (split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]).
rewrite vad_srl3 by lia. unfold w64, SB. rewrite vad_add64 by lia. f_equal. lia.
Qed.

(* ---------- the entry: 0x89e4c .. 0x89ed8 (or 0x89f28) ---------- *)
Lemma vad_stack_field : forall E H mem' cs off k v,
region_ok SEGS E (mrestrict H mem') (YP09.mkRegion (Some 2%nat) (-112) 0 (-112) 0 cs) -> bv_unsigned (ew E 2) = sp0 ->
In (YP09.mkChunk off (CVal 8 (SOff k 0))) cs -> ew E k = w64 v -> 0 <= v < 2 ^ 64 ->
sa_val (aview SEGS H mem') (sp0 + off) 8 v.
Proof using.
intros E H mem' cs off k v HR Hsp Hin Hk Hv. apply vad_sa_of_val_mem.
change 8%nat with (N.to_nat 8).
apply (field_of_region E _ 2 sp0 cs (-112) 0 (-112) 0 off 8 (SOff k 0) v HR Hsp Hin).
- cbn [sv_denot]. rewrite Hk, Z.add_0_r. unfold w64. rewrite unsigned_lit_small by lia. reflexivity.
- change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64). exact Hv.
- cbn. lia.
Qed.
Lemma vad_entry_seed :
st_ok_pi SEGS VAL (Eimg (Ereg regs [w64 SB; w64 L])) vad_ss_entry
  (restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + AF_reac_declared_vlan_add)) mem (seg_rom SEGS)))
/\ sh_ok SEGS vad_Bx vad_entry_SH (Eimg (Ereg regs [w64 SB; w64 L])) (mrestrict (w_H W) mem).
Proof using vad_all.
pose proof HPRE as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof vad_sp as (Hal16 & Hslo & Hshi & _). pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof vad_tab_facts as (T1 & T2 & T3 & _). pose proof vad_n_facts as (N1 & N2 & N3 & N4 & N5 & N6 & N7).
pose proof HADD as ((_ & _ & _ & _ & _ & _ & _ & _ & _ & HNV & _ & HNA & _) & _).
assert (HST : STK_reac_declared_vlan_add = 8304) by reflexivity.
set (E := Eimg (Ereg regs [w64 SB; w64 L])).
assert (Usp : bv_unsigned (ew E 2) = sp0) by (subst E; rewrite (ew_Eimg_Ereg_nat regs _ 2 2%bv eq_refl); reflexivity).
assert (E32 : ew E 32 = w64 SB) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 0)).
assert (E33 : ew E 33 = w64 L) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 1)).
assert (U12 : bv_unsigned (ew E 12) = n)
  by (subst E; rewrite (ew_Eimg_Ereg_nat regs _ 12 12%bv eq_refl), H12; unfold w64; apply unsigned_lit_small; lia).
assert (U33 : bv_unsigned (ew E 33) = L) by (rewrite E33; unfold w64; apply unsigned_lit_small; lia).
assert (E241 : ew E (A_OBJ 0) = Z_to_bv 64 (VAL (A_OBJ 0))) by (subst E; apply Eimg_img; unfold A_OBJ, A_TEXT, A_LIM; lia).
assert (E253 : ew E (A_OBJ 12) = Z_to_bv 64 (VAL (A_OBJ 12))) by (subst E; apply Eimg_img; unfold A_OBJ, A_TEXT, A_LIM; lia).
pose proof (pa_val_range (A_OBJ 0)) as R0. pose proof (pa_val_range (A_OBJ 12)) as R12.
assert (U241 : bv_unsigned (ew E (A_OBJ 0)) = VAL (A_OBJ 0)) by (rewrite E241; apply unsigned_lit_small; lia).
assert (U253 : bv_unsigned (ew E (A_OBJ 12)) = VAL (A_OBJ 12)) by (rewrite E253; apply unsigned_lit_small; lia).
pose proof (pa_obj_img 12 ltac:(lia)) as HcellR. pose proof (pa_obj_img 0 ltac:(lia)) as HgotR. pose proof (pal_got_cell B TL) as HgcD.
destruct (al_const _ _ LAWS _ _ _ _ _ HAR) as (Kcell & _ & Kgot & _).
rewrite (pal_got_shadow B TL), (pal_cell B TL) in Kgot. rewrite (pal_cell B TL) in Kcell.
unfold kImgEnd in *.
split.
- rewrite restrict_mkst_fx. unfold vad_ss_entry. apply pa_entry_st_ok_full.
  + subst E. apply regs_ok_Eimg_Ereg.
  + vm_compute. reflexivity.
  + unfold stack_region, got_regionP, bcell_regionP, vad_nregion0.
    repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
    * rewrite Usp. split; [lia|]. split; [lia|]. split; [|constructor].
      intros o Ho. apply (apresent_writable SEGS). apply Hpres. lia.
    * rewrite U241. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
      constructor; [|constructor].
      apply (chunk_ok_val SEGS E _ (VAL (A_OBJ 0)) 0 8 (SOff (A_OBJ 12) 0) (VAL (A_OBJ 12)));
        [cbn [sv_denot]; rewrite E253, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); lia | cbn; lia |].
      rewrite Z.add_0_r. exact (val_mem_of_rdword SEGS _ _ _ _ Kgot).
    * rewrite U253. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
      constructor; [|constructor].
      apply (chunk_ok_val SEGS E _ (VAL (A_OBJ 12)) 0 8 (SOff 32 0) SB);
        [cbn [sv_denot]; rewrite E32, Z.add_0_r; unfold w64; rewrite unsigned_lit_small by (unfold SB; lia); reflexivity
        | unfold SB; cbn; lia | cbn; lia |].
      rewrite Z.add_0_r. exact (val_mem_of_rdword SEGS _ _ _ _ Kcell).
    * rewrite U12. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
      constructor; [|constructor].
      apply (chunk_ok_val SEGS E _ n 0 4 (SOff 33 0) L);
        [cbn [sv_denot]; rewrite E33, Z.add_0_r; unfold w64; rewrite unsigned_lit_small by lia; reflexivity
        | cbn; lia | cbn; lia |].
      rewrite Z.add_0_r. exact (vad_val_mem_of_sa SEGS _ _ _ _ _ HNV).
  + apply pairwise_disjoint_of_extents. unfold stack_region, got_regionP, bcell_regionP, vad_nregion0, extent_of_region.
    cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite Usp, U241, U253, U12.
    cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd]. repeat split; lia.
  + split; [|split; exact I]. cbn [f_atoms atoms_ok]. unfold afact_ok, vad_spF, vad_SBF. cbn [af_lo af_hi af_al2].
    rewrite Usp, E32, U12, U33. unfold w64. rewrite unsigned_lit_small by (unfold SB; lia).
    change (2 ^ 4) with 16. change (2 ^ 2) with 4. rewrite Z.pow_0_r, Z.mod_1_r.
    repeat split; try lia; assumption.
- unfold sh_ok, vad_entry_SH. apply Forall_cons; [|apply Forall_nil].
  apply (vad_shent_ok E _ _ 12 n 0 4 E32 U12); try lia.
  + rewrite Z.add_0_r. destruct HNA as (_ & _ & _ & HRA & _). exact HRA.
  + intros y Hy. apply N5. lia.
Qed.
Lemma vad_swrap_small : forall z, 0 <= z < 2 ^ 63 -> bv_swrap 64 z = z.
Proof using.
intros z Hz. unfold bv_swrap, bv_half_modulus, bv_modulus. change (2 ^ Z.of_N 64) with (2 ^ 64). change (2 ^ 64 / 2) with (2 ^ 63).
rewrite bv_wrap_small; [lia|]. change (bv_modulus 64) with (2 ^ 64). lia.
Qed.
Lemma vad_bge0 : forall E k v, ew E k = w64 v -> 0 <= v < 2 ^ 63 ->
branch_taken BC_GE (sv_denot E (SLit 0)) (sv_denot E (SOff k 0)) = (v <=? 0).
Proof using.
intros E k v Hk Hv. cbn [branch_taken sv_denot]. rewrite Hk, Z.add_0_r. unfold w64. rewrite unsigned_lit_small by lia.
unfold bv_lts. rewrite !signed_lit. rewrite !zcanon_small by lia. rewrite !vad_swrap_small by lia.
destruct (Z.ltb_spec 0 v); destruct (Z.leb_spec v 0); try reflexivity; lia.
Qed.
(* the frame after the prologue, read back from the stack region of a symbolic state *)
Lemma vad_frm : forall E H mem' cs,
(forall k (r : bv 5), Z.of_nat k = bv_unsigned r -> ew E k = getr regs r) ->
region_ok SEGS E (mrestrict H mem') (YP09.mkRegion (Some 2%nat) (-112) 0 (-112) 0 cs) ->
(forall j r, nth_error vad_saved j = Some r -> In (YP09.mkChunk (-8 - 8 * Z.of_nat j) (CVal 8 (SOff (Z.to_nat r) 0))) cs) ->
vad_frame (aview SEGS H mem').
Proof using.
intros E H mem' cs EE HR Hin j r Hr.
assert (Usp : bv_unsigned (ew E 2) = sp0) by (rewrite (EE 2%nat 2%bv eq_refl); reflexivity).
assert (Hr' : 1 <= r <= 27) by (apply nth_error_In in Hr; cbn in Hr; intuition lia).
replace (sp0 - 8 - 8 * Z.of_nat j) with (sp0 + (-8 - 8 * Z.of_nat j)) by lia.
apply (vad_stack_field E H mem' cs _ (Z.to_nat r)); [exact HR | exact Usp | exact (Hin j r Hr) | |
  pose proof (bv_unsigned_in_range 64 (getr regs (Z_to_bv 5 r))) as HRr; change (bv_modulus 64) with (2 ^ 64) in HRr; exact HRr].
rewrite (EE (Z.to_nat r) (Z_to_bv 5 r)); [unfold w64; rewrite Z_to_bv_bv_unsigned; reflexivity|].
rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 5) with 32. rewrite Z.mod_small by lia. lia.
Qed.
(* at the end of the entry stretch: the cut (journal, frame, sp gp tp, the memory outside the window) *)
Ltac vad_entry_cut K0 K2 K3 K4 HRg HKP EE HJ :=
  lazymatch goal with HS : st_ok_pi _ _ ?Ex ?ssx (restrict _ ?msx) |- _ =>
    let r := eval vm_compute in (nth 0 (ss_mem ssx) (stack_region 0)) in
    pose proof (st_ok_pi_region_nth Ex ssx (restrict _ msx) 0 r HS ltac:(vm_compute; reflexivity)) as HRg;
    cbn [ms_mem restrict] in HRg;
    let EEx := fresh "EEx" in
    assert (EEx : forall k (rr : bv 5), Z.of_nat k = bv_unsigned rr -> ew Ex k = getr regs rr)
      by (let k := fresh "k" in let rr := fresh "rr" in let Hk := fresh "Hk" in let Hrr := fresh "Hrr" in
          intros k rr Hk; pose proof (bv_unsigned_in_range 5 rr) as Hrr; change (bv_modulus 5) with 32 in Hrr;
          cbn [ew ewset]; repeat (rewrite (proj2 (Nat.eqb_neq _ _)) by lia); apply EE; exact Hk);
    let Q2 := fresh "Q2" in let Q3 := fresh "Q3" in let Q4 := fresh "Q4" in
    prreg HS (2%bv : bv 5) Q2; prreg HS (3%bv : bv 5) Q3; prreg HS (4%bv : bv 5) Q4;
    let mdx := lazymatch type of HJ with ajournal _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ?d _ => d end in
    assert (HKP : vad_cut (ms_regs msx) (ms_mem msx) mdx);
    [ split; [split; [exact HJ|]; split;
        [ apply (vad_frm Ex _ _ _ EEx HRg);
          let j := fresh "j" in let rr := fresh "rr" in let Hr := fresh "Hr" in intros j rr Hr;
          do 13 (destruct j as [|j]; [cbn in Hr; injection Hr as <-; vm_compute; repeat first [left; reflexivity | right] |]);
          cbn in Hr; destruct j; discriminate Hr
        | split; [rewrite Q2, (EE 2%nat 2%bv eq_refl); unfold w64, spZ; f_equal; lia|];
          split; [rewrite Q3; apply EE; reflexivity | rewrite Q4; apply EE; reflexivity] ]
      | apply (vad_kept_trans _ _ _ _ _ _ _ (vad_kept_trans _ _ _ _ _ _ _
          (vad_kept_trans _ _ _ _ _ _ _ K0 K2 ltac:(lia) ltac:(lia)) K3 ltac:(lia) ltac:(lia)) K4);
        lia ]
    | ] end.
(* the registers every cut carries, at the end of the entry stretch *)
Ltac vad_entry_regs EE E32 E33 :=
  lazymatch goal with HS : st_ok_pi _ _ _ _ (restrict _ ?msx) |- _ =>
    let R8 := fresh "R8" in let R9 := fresh "R9" in let R18 := fresh "R18" in let R19 := fresh "R19" in
    let R20 := fresh "R20" in let R21 := fresh "R21" in let R24 := fresh "R24" in let R25 := fresh "R25" in
    let R26 := fresh "R26" in
    prreg HS (8%bv : bv 5) R8; prreg HS (9%bv : bv 5) R9; prreg HS (18%bv : bv 5) R18; prreg HS (19%bv : bv 5) R19;
    prreg HS (20%bv : bv 5) R20; prreg HS (21%bv : bv 5) R21; prreg HS (24%bv : bv 5) R24; prreg HS (25%bv : bv 5) R25;
    prreg HS (26%bv : bv 5) R26;
    split; [rewrite R8; apply (eq_trans (EE 12%nat 12%bv eq_refl)); exact H12|];
    split; [rewrite R9; apply (eq_trans (EE 14%nat 14%bv eq_refl)); exact H14|];
    split; [rewrite R18; apply (eq_trans (EE 10%nat 10%bv eq_refl)); exact H10|];
    split; [rewrite R19; apply (eq_trans (EE 13%nat 13%bv eq_refl)); exact H13|];
    split; [rewrite R20; unfold w64; first [reflexivity | apply bv_eq; rewrite !Z_to_bv_unsigned; reflexivity]|];
    split; [rewrite R21; apply (eq_trans (EE 11%nat 11%bv eq_refl)); exact H11|];
    split; [rewrite R24; exact E32|];
    split; [rewrite R25, (EE 12%nat 12%bv eq_refl), H12, E32; apply vad_shx_val; lia|];
    rewrite R26; exact E33 end.
Lemma vad_entry :
(forall r m d, vad_LHc 0 r m d -> SRr SEGS W (mkCfg (mkst r (Z_to_bv 64 (BASE + VAD_LH)) m (seg_rom SEGS)) d) vad_Q) ->
(forall r m d, vad_AFTc r m d -> SRr SEGS W (mkCfg (mkst r (Z_to_bv 64 (BASE + VAD_AFT)) m (seg_rom SEGS)) d) vad_Q) ->
SRr SEGS W (cfg_at SEGS (BASE + AF_reac_declared_vlan_add) regs mem md) vad_Q.
Proof using vad_all.
intros KLH KAFT.
pose proof HPRE as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof vad_sp as (Hal16 & Hslo & Hshi & _). pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof vad_tab_facts as (T1 & T2 & T3 & _). pose proof vad_n_facts as (N1 & N2 & N3 & N4 & N5 & N6 & N7).
pose proof HADD as ((Htz & _ & _ & _ & _ & _ & _ & Hnz & _) & Hpz & _ & _ & _ & _ & _ & _ & Hvid).
assert (HST : STK_reac_declared_vlan_add = 8304) by reflexivity.
destruct vad_entry_seed as [HS SHOK].
pose proof (ajournal_init SEGS B STK_reac_declared_vlan_add vad_FP ly S W regs mem md ch HPRE) as HJ.
assert (HEI : img_env VAL A_LIM (Eimg (Ereg regs [w64 SB; w64 L]))) by apply Eimg_env.
assert (EE : forall k (r : bv 5), Z.of_nat k = bv_unsigned r -> ew (Eimg (Ereg regs [w64 SB; w64 L])) k = getr regs r)
  by (intros k r Hk; apply ew_Eimg_Ereg_nat; exact Hk).
assert (E32 : ew (Eimg (Ereg regs [w64 SB; w64 L])) 32 = w64 SB) by (rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 0)).
assert (E33 : ew (Eimg (Ereg regs [w64 SB; w64 L])) 33 = w64 L) by (rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 1)).
remember (Eimg (Ereg regs [w64 SB; w64 L])) as E eqn:HE. clear HE.
assert (Usp : bv_unsigned (ew E 2) = sp0) by (rewrite (EE 2%nat 2%bv eq_refl); reflexivity).
assert (U10 : U E (SOff 10 0) = tab) by (apply U_atom; [rewrite (EE 10%nat 10%bv eq_refl); exact H10 | lia]).
assert (U12 : U E (SOff 12 0) = n) by (apply U_atom; [rewrite (EE 12%nat 12%bv eq_refl); exact H12 | lia]).
assert (U13 : U E (SOff 13 0) = par).
{ apply U_atom; [rewrite (EE 13%nat 13%bv eq_refl); exact H13|]. destruct HADD as (_ & _ & _ & HPA & _). destruct HPA as (P0 & P1 & _). lia. }
unfold cfg_at. change (w64 (BASE + AF_reac_declared_vlan_add)) with (Z_to_bv 64 (BASE + AF_reac_declared_vlan_add)).
(* 0x89e4c .. 0x89e88: the frame, s4 = -1, beqz a0 *)
paj_run_tok RUN HS HJ SHOK Bspan.
{ awr_ok_tac; exact Usp. }
vad_md.
vad_keep_win HFr KEEP0 (spZ regs - STK_reac_declared_vlan_add) (spZ regs) Usp. clear HF HFr HG.
psrr_branch_tok RUN BR HS SHOK Bspan.
{ exfalso. rewrite branch_eq_U, U10, U_SLit in Hc. change (zcanon 0) with 0 in Hc. apply Z.eqb_eq in Hc. lia. }
clear Hc.
(* 0x89e8c .. 0x89e98: s0 = n, beqz a2 (decided by the fact on atom 12), s3 = parent, beqz a3 *)
paj_run_tok RUN HS HJ SHOK Bspan.
{ awr_ok_tac; exact Usp. }
vad_md.
vad_keep_win HFr KEEP2 (spZ regs - STK_reac_declared_vlan_add) (spZ regs) Usp. clear HF HFr HG.
psrr_branch_tok RUN BR HS SHOK Bspan.
{ exfalso. rewrite branch_eq_U, U13, U_SLit in Hc. change (zcanon 0) with 0 in Hc. apply Z.eqb_eq in Hc. lia. }
clear Hc.
(* 0x89e9c .. 0x89ec8: s1, s5, s2, the shadow base, s9, inline check 1, s10 = count, blez *)
paj_run_tok RUN HS HJ SHOK Bspan.
{ awr_ok_tac; exact Usp. }
vad_md.
vad_keep_win HFr KEEP3 (spZ regs - STK_reac_declared_vlan_add) (spZ regs) Usp. clear HF HFr HG.
psrr_branch_tok RUN BR HS SHOK Bspan.
- (* blez taken: no entry; 0x89f28 *)
  lazymatch type of Hc with context [sv_denot ?Ex (SOff 33 0)] =>
    assert (E33x : ew Ex 33 = w64 L) by (cbn [ew ewset Nat.eqb]; exact E33) end.
  rewrite (vad_bge0 _ 33 L E33x) in Hc by lia. apply Z.leb_le in Hc.
  assert (Ht0 : t = []) by (destruct t; [reflexivity | cbn [length] in Hc; lia]).
  paj_run_to_tok RUNTO HS HJ SHOK Bspan VAD_AFT.
  { awr_ok_tac; cbn [ew ewset Nat.eqb]; exact Usp. }
  vad_md.
  vad_keep_win HFr KEEP4 (spZ regs - STK_reac_declared_vlan_add) (spZ regs) Usp. clear HF HFr HG.
  pmkst HS.
  vad_entry_cut KEEP0 KEEP2 KEEP3 KEEP4 HRg HKP EE HJ.
  apply KAFT. split; [|split].
  + exact HKP.
  + vad_entry_regs EE E32 E33.
  + rewrite Ht0. reflexivity.
- (* blez not taken: the search from entry 0; 0x89ed8 *)
  lazymatch type of Hc with context [sv_denot ?Ex (SOff 33 0)] =>
    assert (E33x : ew Ex 33 = w64 L) by (cbn [ew ewset Nat.eqb]; exact E33) end.
  rewrite (vad_bge0 _ 33 L E33x) in Hc by lia. apply Z.leb_gt in Hc.
  paj_run_to_tok RUNTO HS HJ SHOK Bspan VAD_LH.
  { awr_ok_tac; cbn [ew ewset Nat.eqb]; exact Usp. }
  vad_md.
  vad_keep_win HFr KEEP4 (spZ regs - STK_reac_declared_vlan_add) (spZ regs) Usp. clear HF HFr HG.
  pmkst HS.
  vad_entry_cut KEEP0 KEEP2 KEEP3 KEEP4 HRg HKP EE HJ.
  apply KLH. split; [exact HKP|]. split; [vad_entry_regs EE E32 E33|].
  split; [lia|]. split; [reflexivity|].
  prreg HS (23%bv : bv 5) Q23. prreg HS (22%bv : bv 5) Q22. prreg HS (27%bv : bv 5) Q27.
  split; [rewrite Q23, (EE 10%nat 10%bv eq_refl), H10; unfold w64; f_equal; lia|].
  split; [rewrite Q22, (EE 10%nat 10%bv eq_refl), H10; unfold w64; rewrite unsigned_lit_small by lia; f_equal; lia|].
  rewrite Q27, E33. unfold w64. f_equal. lia.
Qed.

(* a cut carried to a later state whose memory differs only in a window below the frame *)
Lemma vad_cut_kept : forall regs1 mem1 md1 regs2 mem2 md2 lo hi,
vad_cut regs1 mem1 md1 ->
ajournal SEGS B STK_reac_declared_vlan_add sp0 vad_FP ly S W mem md [] ly S W mem2 md2 0 ->
vad_kept (rdW W mem1) (rdW W mem2) lo hi -> sp0 - STK_reac_declared_vlan_add <= lo -> hi <= sp0 - 112 ->
getr regs2 2 = getr regs1 2 -> getr regs2 3 = getr regs1 3 -> getr regs2 4 = getr regs1 4 ->
vad_cut regs2 mem2 md2.
Proof using vad_all.
intros regs1 mem1 md1 regs2 mem2 md2 lo hi ((HJ & HFR & R2 & R3 & R4) & HK) HJ2 HK2 Hlo Hhi Q2 Q3 Q4.
pose proof vad_sp as (Hal16 & Hslo & Hshi & _). pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (HST : STK_reac_declared_vlan_add = 8304) by reflexivity.
split; [split; [exact HJ2|]; split|].
- intros j r Hr. assert (Hj : (j < 13)%nat) by (change 13%nat with (length vad_saved); apply (proj1 (nth_error_Some vad_saved j)); rewrite Hr; discriminate).
  apply (vad_sa_val_keep (rdW W mem1) _ (fun x => 0 <= x < 2 ^ 64 /\ ~ (lo <= x < hi))); [intros x [Hx1 Hx2]; exact (HK2 x Hx1 Hx2) | exact (HFR j r Hr) |].
  intros k Hk. cbv beta. lia.
- split; [rewrite Q2; exact R2|]. split; [rewrite Q3; exact R3 | rewrite Q4; exact R4].
- intros x Hx Hn. destruct (Z_lt_le_dec x lo) as [Hl|Hl]; [rewrite (HK2 x Hx) by lia; exact (HK x Hx Hn)|].
  destruct (Z_lt_le_dec x hi) as [Hh|Hh]; [exfalso; apply Hn; lia|]. rewrite (HK2 x Hx) by lia. exact (HK x Hx Hn).
Qed.
(* the extra words of a seed *)
Lemma vad_ex_w64 : forall regs1 (l : list Z) j, (32 + j < A_TEXT)%nat -> (j < length l)%nat ->
ew (Eimg (Ereg regs1 (map w64 l))) (32 + j) = w64 (nth j l 0).
Proof using.
intros regs1 l j H1 H2. rewrite Eimg_low by exact H1. rewrite ew_Ereg_extra.
rewrite (nth_indep _ _ (w64 0)) by (rewrite length_map; exact H2). apply map_nth.
Qed.

(* ---------- the seed at the loop head (0x89ed8), entry i ---------- *)
Lemma vad_lh_seed : forall (i : nat) vi regs1 mem1,
(i < length t)%nat -> 0 <= vi < 65536 ->
getr regs1 2 = w64 (sp0 - 112) -> getr regs1 24 = w64 SB ->
getr regs1 23 = w64 (tab + 18 * Z.of_nat i) -> getr regs1 22 = w64 (tab + 18 * Z.of_nat i + 16) ->
sa_val (rdW W mem1) (tab + 18 * Z.of_nat i + 16) 2 vi ->
range_addressable (rdW W mem1) SHADOW_OFF (tab + 18 * Z.of_nat i) 18 ->
st_ok_pi SEGS VAL (Eimg (Ereg regs1 (map w64 [SB; tab + 18 * Z.of_nat i; vi]))) vad_ss_lh
  (restrict (w_H W) (mkst regs1 (Z_to_bv 64 (BASE + VAD_LH)) mem1 (seg_rom SEGS)))
/\ sh_ok SEGS vad_Bx vad_lh_SH (Eimg (Ereg regs1 (map w64 [SB; tab + 18 * Z.of_nat i; vi]))) (mrestrict (w_H W) mem1).
Proof using vad_all.
intros i vi regs1 mem1 Hi Hvi R2 R24 R23 R22 VV RA.
pose proof vad_sp as (Hal16 & Hslo & Hshi & _). pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof vad_tab_facts as (T1 & T2 & T3 & T4 & T5 & T6).
assert (HST : STK_reac_declared_vlan_add = 8304) by reflexivity.
set (Q := tab + 18 * Z.of_nat i) in *.
set (E := Eimg (Ereg regs1 (map w64 [SB; Q; vi]))).
assert (EE : forall k (r : bv 5), Z.of_nat k = bv_unsigned r -> ew E k = getr regs1 r) by (intros k r Hk; apply ew_Eimg_Ereg_nat; exact Hk).
assert (Usp : bv_unsigned (ew E 2) = sp0 - 112) by (rewrite (EE 2%nat 2%bv eq_refl), R2; apply unsigned_lit_small; lia).
pose proof (vad_ex_w64 regs1 [SB; Q; vi] 0 ltac:(unfold A_TEXT; lia) ltac:(cbn; lia)) as E32.
pose proof (vad_ex_w64 regs1 [SB; Q; vi] 1 ltac:(unfold A_TEXT; lia) ltac:(cbn; lia)) as E33.
pose proof (vad_ex_w64 regs1 [SB; Q; vi] 2 ltac:(unfold A_TEXT; lia) ltac:(cbn; lia)) as E34.
cbn [nth Nat.add] in E32, E33, E34. fold E in E32, E33, E34.
assert (E32u : bv_unsigned (ew E 32) = SB) by (rewrite E32; apply unsigned_lit_small; unfold SB; lia).
assert (E33u : bv_unsigned (ew E 33) = Q) by (rewrite E33; apply unsigned_lit_small; lia).
assert (E34u : bv_unsigned (ew E 34) = vi) by (rewrite E34; apply unsigned_lit_small; lia).
split.
- rewrite restrict_mkst_fx. unfold vad_ss_lh. apply pa_entry_st_ok_full.
  + vad_regs_ok EE ltac:(rewrite ?E32u, ?E33u).
  + vm_compute. reflexivity.
  + apply Forall_cons; [|apply Forall_nil]. unfold region_ok, vad_entryR.
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val]. rewrite E33u.
    split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
    apply Forall_cons; [|apply Forall_nil].
    apply (chunk_ok_val SEGS E _ Q 16 2 (SOff 34 0) vi); [cbn [sv_denot]; rewrite E34u, Z.add_0_r; try reflexivity | cbn; lia | cbn; lia |].
    apply vad_val_mem_of_sa. exact VV.
  + cbn. tauto.
  + split; [|split; exact I]. cbn [f_atoms atoms_ok]. unfold afact_ok, vad_spF, vad_SBF, vad_PTRF. cbn [af_lo af_hi af_al2].
    rewrite Usp, E32u, E33u, E34u. change (2 ^ 4) with 16. rewrite !Z.pow_0_r, !Z.mod_1_r.
    repeat split; try lia; rewrite Zminus_mod, Hal16; reflexivity.
- unfold sh_ok, vad_lh_SH. apply Forall_cons; [|apply Forall_nil].
  apply (vad_shent_ok E _ _ 33 Q 0 18 E32 E33u); try lia.
  + rewrite Z.add_0_r. exact RA.
  + intros y Hy. apply T5. lia.
Qed.

(* ---------- the latch: 0x89f00 .. 0x89f10, then the loop head or 0x89f28 ---------- *)
Lemma vad_lt_seed : forall (i : nat) regs1 mem1,
(i < length t)%nat ->
getr regs1 2 = w64 (sp0 - 112) -> getr regs1 24 = w64 SB ->
getr regs1 23 = w64 (tab + 18 * Z.of_nat i) -> getr regs1 22 = w64 (tab + 18 * Z.of_nat i + 16) ->
getr regs1 27 = w64 (L - Z.of_nat i) ->
st_ok_pi SEGS VAL (Eimg (Ereg regs1 (map w64 [SB; tab + 18 * Z.of_nat i; L - Z.of_nat i]))) vad_ss_lt
  (restrict (w_H W) (mkst regs1 (Z_to_bv 64 (BASE + VAD_LT)) mem1 (seg_rom SEGS)))
/\ sh_ok SEGS vad_Bx [] (Eimg (Ereg regs1 (map w64 [SB; tab + 18 * Z.of_nat i; L - Z.of_nat i]))) (mrestrict (w_H W) mem1).
Proof using vad_all.
intros i regs1 mem1 Hi R2 R24 R23 R22 R27.
pose proof vad_sp as (Hal16 & Hslo & Hshi & _). pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof vad_tab_facts as (T1 & T2 & T3 & T4 & T5 & T6).
assert (HST : STK_reac_declared_vlan_add = 8304) by reflexivity.
set (Q := tab + 18 * Z.of_nat i) in *.
set (E := Eimg (Ereg regs1 (map w64 [SB; Q; L - Z.of_nat i]))).
assert (EE : forall k (r : bv 5), Z.of_nat k = bv_unsigned r -> ew E k = getr regs1 r) by (intros k r Hk; apply ew_Eimg_Ereg_nat; exact Hk).
assert (Usp : bv_unsigned (ew E 2) = sp0 - 112) by (rewrite (EE 2%nat 2%bv eq_refl), R2; apply unsigned_lit_small; lia).
pose proof (vad_ex_w64 regs1 [SB; Q; L - Z.of_nat i] 0 ltac:(unfold A_TEXT; lia) ltac:(cbn; lia)) as E32.
pose proof (vad_ex_w64 regs1 [SB; Q; L - Z.of_nat i] 1 ltac:(unfold A_TEXT; lia) ltac:(cbn; lia)) as E33.
pose proof (vad_ex_w64 regs1 [SB; Q; L - Z.of_nat i] 2 ltac:(unfold A_TEXT; lia) ltac:(cbn; lia)) as E34.
cbn [nth Nat.add] in E32, E33, E34. fold E in E32, E33, E34.
assert (E32u : bv_unsigned (ew E 32) = SB) by (rewrite E32; apply unsigned_lit_small; unfold SB; lia).
assert (E33u : bv_unsigned (ew E 33) = Q) by (rewrite E33; apply unsigned_lit_small; lia).
assert (E34u : bv_unsigned (ew E 34) = L - Z.of_nat i) by (rewrite E34; apply unsigned_lit_small; lia).
split; [|apply Forall_nil].
rewrite restrict_mkst_fx. unfold vad_ss_lt. apply pa_entry_st_ok_full.
- vad_regs_ok EE ltac:(rewrite ?E32u, ?E33u, ?E34u).
- vm_compute. reflexivity.
- apply Forall_nil.
- cbn. tauto.
- split; [|split; exact I]. cbn [f_atoms atoms_ok]. unfold afact_ok, vad_spF, vad_SBF, vad_PTRF. cbn [af_lo af_hi af_al2].
  rewrite Usp, E32u, E33u, E34u. change (2 ^ 4) with 16. rewrite !Z.pow_0_r, !Z.mod_1_r.
  repeat split; try lia; rewrite Zminus_mod, Hal16; reflexivity.
Qed.
Lemma vad_latch : forall i regs1 mem1 md1, vad_LTc i regs1 mem1 md1 ->
((Datatypes.S i < length t)%nat -> forall r m d, vad_LHc (Datatypes.S i) r m d ->
  SRr SEGS W (mkCfg (mkst r (Z_to_bv 64 (BASE + VAD_LH)) m (seg_rom SEGS)) d) vad_Q) ->
(forall r m d, vad_AFTc r m d -> SRr SEGS W (mkCfg (mkst r (Z_to_bv 64 (BASE + VAD_AFT)) m (seg_rom SEGS)) d) vad_Q) ->
SRr SEGS W (mkCfg (mkst regs1 (Z_to_bv 64 (BASE + VAD_LT)) mem1 (seg_rom SEGS)) md1) vad_Q.
Proof using vad_all.
intros i regs1 mem1 md1 (HCUT & (R8 & R9 & R18 & R19 & R20 & R21 & R24 & R25 & R26) & Hi & HEX & R23 & R22 & R27) KLH KAFT.
pose proof HCUT as ((HJ & HFR & R2 & R3 & R4) & HK).
pose proof vad_sp as (Hal16 & Hslo & Hshi & _). pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof vad_tab_facts as (T1 & T2 & T3 & T4 & T5 & T6).
assert (HST : STK_reac_declared_vlan_add = 8304) by reflexivity.
destruct (vad_lt_seed i regs1 mem1 Hi R2 R24 R23 R22 R27) as [HS SHOK].
set (Q := tab + 18 * Z.of_nat i) in *.
assert (HEI : img_env VAL A_LIM (Eimg (Ereg regs1 (map w64 [SB; Q; L - Z.of_nat i])))) by apply Eimg_env.
assert (EE : forall k (r : bv 5), Z.of_nat k = bv_unsigned r -> ew (Eimg (Ereg regs1 (map w64 [SB; Q; L - Z.of_nat i]))) k = getr regs1 r)
  by (intros k r Hk; apply ew_Eimg_Ereg_nat; exact Hk).
pose proof (vad_ex_w64 regs1 [SB; Q; L - Z.of_nat i] 0 ltac:(unfold A_TEXT; lia) ltac:(cbn; lia)) as E32.
pose proof (vad_ex_w64 regs1 [SB; Q; L - Z.of_nat i] 1 ltac:(unfold A_TEXT; lia) ltac:(cbn; lia)) as E33.
pose proof (vad_ex_w64 regs1 [SB; Q; L - Z.of_nat i] 2 ltac:(unfold A_TEXT; lia) ltac:(cbn; lia)) as E34.
cbn [nth Nat.add] in E32, E33, E34.
remember (Eimg (Ereg regs1 (map w64 [SB; Q; L - Z.of_nat i]))) as E eqn:HE. clear HE.
assert (Usp : bv_unsigned (ew E 2) = sp0 - 112) by (rewrite (EE 2%nat 2%bv eq_refl), R2; apply unsigned_lit_small; lia).
assert (E33u : bv_unsigned (ew E 33) = Q) by (rewrite E33; apply unsigned_lit_small; lia).
assert (E34u : bv_unsigned (ew E 34) = L - Z.of_nat i) by (rewrite E34; apply unsigned_lit_small; lia).
paj_run_tok RUN HS HJ SHOK Bspan.
{ awr_ok_tac; exact Usp. }
vad_md.
vad_keep_empty HFr KEEP1. clear HF HFr HG.
assert (KEEPk : vad_kept (rdW W mem1) (rdW W (ms_mem ms)) (sp0 - STK_reac_declared_vlan_add) (sp0 - STK_reac_declared_vlan_add)).
{ intros x Hx _. exact (KEEP1 x Hx). }
psrr_branch_tok RUN BR HS SHOK Bspan.
- (* s11 - 1 <> 0: entry i + 1 *)
  assert (HiN : (Datatypes.S i < length t)%nat).
  { rewrite branch_ne_U, U_SOff, U_SLit, E34u in Hc. change (zcanon 0) with 0 in Hc.
    rewrite zcanon_small in Hc by lia. apply negb_true_iff, Z.eqb_neq in Hc. lia. }
  paj_run_to_tok RUNTO HS HJ SHOK Bspan VAD_LH.
  { awr_ok_tac; exact Usp. }
  vad_md.
  vad_keep_empty HFr KEEP2. clear HF HFr HG.
  pmkst HS.
  prreg HS (2%bv : bv 5) P2. prreg HS (3%bv : bv 5) P3. prreg HS (4%bv : bv 5) P4.
  prreg HS (8%bv : bv 5) P8. prreg HS (9%bv : bv 5) P9. prreg HS (18%bv : bv 5) P18. prreg HS (19%bv : bv 5) P19.
  prreg HS (20%bv : bv 5) P20. prreg HS (21%bv : bv 5) P21. prreg HS (22%bv : bv 5) P22. prreg HS (23%bv : bv 5) P23.
  prreg HS (24%bv : bv 5) P24. prreg HS (25%bv : bv 5) P25. prreg HS (26%bv : bv 5) P26. prreg HS (27%bv : bv 5) P27.
  apply (KLH HiN). split; [|split; [|split; [exact HiN|]]].
  + apply (vad_cut_kept regs1 mem1 md1 _ _ _ (sp0 - STK_reac_declared_vlan_add) (sp0 - STK_reac_declared_vlan_add) HCUT HJ); [| lia | lia | rewrite P2; apply EE; reflexivity
      | rewrite P3; apply EE; reflexivity | rewrite P4; apply EE; reflexivity].
    intros x Hx _. rewrite (KEEP2 x Hx). exact (KEEP1 x Hx).
  + split; [rewrite P8; rewrite (EE 8%nat 8%bv eq_refl); exact R8|].
    split; [rewrite P9; rewrite (EE 9%nat 9%bv eq_refl); exact R9|].
    split; [rewrite P18; rewrite (EE 18%nat 18%bv eq_refl); exact R18|].
    split; [rewrite P19; rewrite (EE 19%nat 19%bv eq_refl); exact R19|].
    split; [rewrite P20; rewrite (EE 20%nat 20%bv eq_refl); exact R20|].
    split; [rewrite P21; rewrite (EE 21%nat 21%bv eq_refl); exact R21|].
    split; [rewrite P24; exact E32|].
    split; [rewrite P25; rewrite (EE 25%nat 25%bv eq_refl); exact R25|].
    rewrite P26; rewrite (EE 26%nat 26%bv eq_refl); exact R26.
  + split; [exact HEX|].
    split; [rewrite P23, E33u; unfold w64; f_equal; subst Q; lia|].
    split; [rewrite P22, E33u; unfold w64; f_equal; subst Q; lia|].
    rewrite P27, E34u. unfold w64. f_equal. lia.
- (* s11 - 1 = 0: the search is done, no entry matched; 0x89f28 *)
  assert (HiN : Datatypes.S i = length t).
  { rewrite branch_ne_U, U_SOff, U_SLit, E34u in Hc. change (zcanon 0) with 0 in Hc.
    rewrite zcanon_small in Hc by lia. apply negb_false_iff, Z.eqb_eq in Hc. lia. }
  paj_run_to_tok RUNTO HS HJ SHOK Bspan VAD_AFT.
  { awr_ok_tac; exact Usp. }
  vad_md.
  vad_keep_empty HFr KEEP2. clear HF HFr HG.
  pmkst HS.
  prreg HS (2%bv : bv 5) P2. prreg HS (3%bv : bv 5) P3. prreg HS (4%bv : bv 5) P4.
  prreg HS (8%bv : bv 5) P8. prreg HS (9%bv : bv 5) P9. prreg HS (18%bv : bv 5) P18. prreg HS (19%bv : bv 5) P19.
  prreg HS (20%bv : bv 5) P20. prreg HS (21%bv : bv 5) P21.
  prreg HS (24%bv : bv 5) P24. prreg HS (25%bv : bv 5) P25. prreg HS (26%bv : bv 5) P26.
  apply KAFT. split; [|split].
  + apply (vad_cut_kept regs1 mem1 md1 _ _ _ (sp0 - STK_reac_declared_vlan_add) (sp0 - STK_reac_declared_vlan_add) HCUT HJ); [| lia | lia | rewrite P2; apply EE; reflexivity
      | rewrite P3; apply EE; reflexivity | rewrite P4; apply EE; reflexivity].
    intros x Hx _. rewrite (KEEP2 x Hx). exact (KEEP1 x Hx).
  + split; [rewrite P8; rewrite (EE 8%nat 8%bv eq_refl); exact R8|].
    split; [rewrite P9; rewrite (EE 9%nat 9%bv eq_refl); exact R9|].
    split; [rewrite P18; rewrite (EE 18%nat 18%bv eq_refl); exact R18|].
    split; [rewrite P19; rewrite (EE 19%nat 19%bv eq_refl); exact R19|].
    split; [rewrite P20; rewrite (EE 20%nat 20%bv eq_refl); exact R20|].
    split; [rewrite P21; rewrite (EE 21%nat 21%bv eq_refl); exact R21|].
    split; [rewrite P24; exact E32|].
    split; [rewrite P25; rewrite (EE 25%nat 25%bv eq_refl); exact R25|].
    rewrite P26; rewrite (EE 26%nat 26%bv eq_refl); exact R26.
  + rewrite HEX. apply vad_existsb_skipn_all. lia.
Qed.


(* ---------- the bytes the append writes: the call may write them (awr_byte) ---------- *)
(* the shadow facts of a range survive a change of the memory away from its shadow cells *)
Lemma vad_ra_keep : forall (rd rd' : reader) (P : Z -> Prop) a len, (forall y, P y -> rd' y = rd y) ->
range_addressable rd SHADOW_OFF a len -> (forall x, a <= x < a + len -> P (shadow_of_addr SHADOW_OFF x)) ->
range_addressable rd' SHADOW_OFF a len.
Proof using. intros rd rd' P a len HK H HP x Hx. rewrite (HK _ (HP x Hx)). exact (H x Hx). Qed.
Lemma vad_hull_keep : forall (rd rd' : reader) (P : Z -> Prop) a len, (forall y, P y -> rd' y = rd y) ->
shadow_hull_vis rd a len ->
(forall s, shadow_addr a / 8 * 8 <= s < shadow_addr (a + len - 1) / 8 * 8 + 8 -> P s) ->
shadow_hull_vis rd' a len.
Proof using. intros rd rd' P a len HK H HP s Hs. rewrite (HK _ (HP s Hs)). exact (H s Hs). Qed.
Lemma vad_FP_app : existsb (vad_match vid p) t = false -> L < max ->
vad_FP = [(tab + 18 * L, tab + 18 * L + 18); (n, n + 4)].
Proof using.
intros HEX LT. unfold vad_FP, vtab_W. rewrite (vad_vlan_add_app t max p vid HEX LT). cbn [snd].
rewrite length_app. cbn [length]. unfold seg_spec.RVLAN_SIZE.
replace (length t <? length t + 1)%nat with true by (symmetry; apply Nat.ltb_lt; lia).
cbn [app]. f_equal. f_equal. lia.
Qed.
Lemma vad_awr_tab : forall a, existsb (vad_match vid p) t = false -> L < max ->
tab + 18 * L <= a < tab + 18 * L + 18 ->
awr_byte SEGS B STK_reac_declared_vlan_add sp0 vad_FP (ablocks B ly S) (ablocks B ly S) (frames S) ly [] a.
Proof using vad_all.
intros a HEX LT Ha. pose proof HADD as ((_ & _ & _ & _ & (b & m & Hbm & Hb1 & Hb2) & _) & _).
pose proof (req_size_pos0 m ltac:(unfold seg_spec.RVLAN_SIZE in *; lia)) as [_ Hreq].
right; left. split.
- rewrite (vad_FP_app HEX LT). exists (tab + 18 * L, tab + 18 * L + 18). split; [left; reflexivity | cbn [fst snd]; lia].
- exists b, m. split; [exact Hbm|]. unfold seg_spec.RVLAN_SIZE in *. lia.
Qed.
Lemma vad_awr_n : forall a, existsb (vad_match vid p) t = false -> L < max -> n <= a < n + 4 ->
awr_byte SEGS B STK_reac_declared_vlan_add sp0 vad_FP (ablocks B ly S) (ablocks B ly S) (frames S) ly [] a.
Proof using vad_all.
intros a HEX LT Ha. pose proof HADD as ((_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HDST & _) & _).
assert (HF : inFP vad_FP a) by (rewrite (vad_FP_app HEX LT); exists (n, n + 4); split; [right; left; reflexivity | cbn [fst snd]; lia]).
destruct HDST as [((cid & pos & Hin & Hcid & Hf1 & Hf2) & _) | [((b & m & Hbm & Hb1 & Hb2) & _) | (Hs1 & Hs2 & _)]].
- right; right; right; right. right; right. split; [exact HF|]. exists cid, pos. split; [exact Hin|]. left. unfold in_zr. cbn [fst snd]. lia.
- pose proof (req_size_pos0 m ltac:(lia)) as [_ Hreq].
  right; left. split; [exact HF|]. exists b, m. split; [exact Hbm|]. lia.
- right; right; right; right. right; left. split; [exact HF|]. lia.
Qed.
Lemma vad_sa_bytes_app : forall rd a l1 l2, sa_bytes rd a (l1 ++ l2) <-> sa_bytes rd a l1 /\ sa_bytes rd (a + Z.of_nat (length l1)) l2.
Proof using.
intros rd a l1 l2. split.
- intros H. split.
  + intros i Hi. rewrite (H i ltac:(rewrite length_app; lia)). rewrite app_nth1 by exact Hi. reflexivity.
  + intros i Hi. replace (a + Z.of_nat (length l1) + Z.of_nat i) with (a + Z.of_nat (length l1 + i)) by lia.
    rewrite (H (length l1 + i)%nat ltac:(rewrite length_app; lia)). rewrite app_nth2 by lia.
    replace (length l1 + i - length l1)%nat with i by lia. reflexivity.
- intros [H1 H2] i Hi. rewrite length_app in Hi. destruct (Nat.lt_ge_cases i (length l1)) as [Hlt|Hge].
  + rewrite (H1 i Hlt). rewrite app_nth1 by exact Hlt. reflexivity.
  + replace (a + Z.of_nat i) with (a + Z.of_nat (length l1) + Z.of_nat (i - length l1)) by lia.
    rewrite (H2 (i - length l1)%nat ltac:(lia)). rewrite app_nth2 by exact Hge. reflexivity.
Qed.

(* ---------- the store stretch: 0x89f80 .. 0x89fac ---------- *)
(* at 0x89f80 on the append path: a0 = &tab[count].vid; the entry's first 16 bytes are those of the new entry *)
Definition vad_STc (regs1 : bvmap 5 word) (mem1 : word -> option byte) (md1 : Model) : Prop :=
vad_cutE regs1 mem1 md1 /\ L < max /\ existsb (vad_match vid p) t = false /\
getr regs1 8 = w64 n /\ getr regs1 9 = w64 vid /\ getr regs1 24 = w64 SB /\ getr regs1 10 = w64 (tab + 18 * L + 16) /\
(forall x, 0 <= x < 2 ^ 64 -> ~ (sp0 - STK_reac_declared_vlan_add <= x < sp0) -> ~ (tab + 18 * L <= x < tab + 18 * L + 18) ->
  rdW W mem1 x = rdW W mem x) /\
(exists f16, length f16 = 16%nat /\ sa_bytes (rdW W mem1) (tab + 18 * L) f16 /\
  seg_spec.rvlan_enc (firstn 15 (cut_nul p), vid) (f16 ++ Mem.le2 (Z_to_bv 64 vid))).
Lemma vad_st_seed : forall regs1 mem1,
L < max ->
getr regs1 2 = w64 (sp0 - 112) -> getr regs1 8 = w64 n -> getr regs1 24 = w64 SB -> getr regs1 10 = w64 (tab + 18 * L + 16) ->
sa_val (rdW W mem1) n 4 L ->
range_addressable (rdW W mem1) SHADOW_OFF (tab + 18 * L + 16) 2 ->
range_addressable (rdW W mem1) SHADOW_OFF n 4 ->
(forall a, tab + 18 * L + 16 <= a < tab + 18 * L + 18 -> apresent (w_H W) mem1 a) ->
(forall a, n <= a < n + 4 -> apresent (w_H W) mem1 a) ->
st_ok_pi SEGS VAL (Eimg (Ereg regs1 (map w64 [SB; n; L; tab + 18 * L]))) vad_ss_st
  (restrict (w_H W) (mkst regs1 (Z_to_bv 64 (BASE + VAD_ST)) mem1 (seg_rom SEGS)))
/\ sh_ok SEGS vad_Bx vad_st_SH (Eimg (Ereg regs1 (map w64 [SB; n; L; tab + 18 * L]))) (mrestrict (w_H W) mem1).
Proof using vad_all.
intros regs1 mem1 LT R2 R8 R24 R10 VN RA RAN PD PN.
pose proof vad_sp as (Hal16 & Hslo & Hshi & _). pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof vad_tab_facts as (T1 & T2 & T3 & T4 & T5 & T6). pose proof vad_n_facts as (N1 & N2 & N3 & N4 & N5 & N6 & N7).
assert (HST : STK_reac_declared_vlan_add = 8304) by reflexivity.
set (D := tab + 18 * L) in *.
set (E := Eimg (Ereg regs1 (map w64 [SB; n; L; D]))).
assert (EE : forall k (r : bv 5), Z.of_nat k = bv_unsigned r -> ew E k = getr regs1 r) by (intros k r Hk; apply ew_Eimg_Ereg_nat; exact Hk).
assert (Usp : bv_unsigned (ew E 2) = sp0 - 112) by (rewrite (EE 2%nat 2%bv eq_refl), R2; apply unsigned_lit_small; lia).
pose proof (vad_ex_w64 regs1 [SB; n; L; D] 0 ltac:(unfold A_TEXT; lia) ltac:(cbn; lia)) as E32.
pose proof (vad_ex_w64 regs1 [SB; n; L; D] 1 ltac:(unfold A_TEXT; lia) ltac:(cbn; lia)) as E33.
pose proof (vad_ex_w64 regs1 [SB; n; L; D] 2 ltac:(unfold A_TEXT; lia) ltac:(cbn; lia)) as E34.
pose proof (vad_ex_w64 regs1 [SB; n; L; D] 3 ltac:(unfold A_TEXT; lia) ltac:(cbn; lia)) as E35.
cbn [nth Nat.add] in E32, E33, E34, E35. fold E in E32, E33, E34, E35.
assert (E32u : bv_unsigned (ew E 32) = SB) by (rewrite E32; apply unsigned_lit_small; unfold SB; lia).
assert (E33u : bv_unsigned (ew E 33) = n) by (rewrite E33; apply unsigned_lit_small; lia).
assert (E34u : bv_unsigned (ew E 34) = L) by (rewrite E34; apply unsigned_lit_small; lia).
assert (E35u : bv_unsigned (ew E 35) = D) by (rewrite E35; apply unsigned_lit_small; lia).
split.
- rewrite restrict_mkst_fx. unfold vad_ss_st. apply pa_entry_st_ok_full.
  + vad_regs_ok EE ltac:(rewrite ?E32u, ?E33u, ?E35u).
  + vm_compute. reflexivity.
  + unfold vad_vidR, vad_nregionS. apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]]; unfold region_ok;
      cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
    * rewrite E35u. split; [lia|]. split; [lia|]. split; [|apply Forall_nil].
      intros o Ho. apply (apresent_writable SEGS). apply PD. lia.
    * rewrite E33u. split; [lia|]. split; [lia|]. split.
      { intros o Ho. apply (apresent_writable SEGS). apply PN. lia. }
      apply Forall_cons; [|apply Forall_nil].
      apply (chunk_ok_val SEGS E _ n 0 4 (SOff 34 0) L); [cbn [sv_denot]; rewrite E34u, Z.add_0_r; try reflexivity | cbn; lia | cbn; lia |].
      rewrite Z.add_0_r. apply vad_val_mem_of_sa. exact VN.
  + apply pairwise_disjoint_of_extents. unfold vad_vidR, vad_nregionS, extent_of_region.
    cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite E33u, E35u.
    cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd]. repeat split; lia.
  + split; [|split; exact I]. cbn [f_atoms atoms_ok]. unfold afact_ok, vad_spF, vad_SBF, vad_PTRF. cbn [af_lo af_hi af_al2].
    rewrite Usp, E32u, E33u, E34u, E35u. change (2 ^ 4) with 16. change (2 ^ 2) with 4. rewrite !Z.pow_0_r, !Z.mod_1_r.
    repeat split; try lia; first [rewrite Zminus_mod, Hal16; reflexivity | assumption].
- unfold sh_ok, vad_st_SH. apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]].
  + apply (vad_shent_ok E _ _ 35 D 16 18 E32 E35u); try lia.
    * exact RA.
    * intros y Hy. apply T5. lia.
  + apply (vad_shent_ok E _ _ 33 n 0 4 E32 E33u); try lia.
    * rewrite Z.add_0_r. exact RAN.
    * intros y Hy. apply N5. lia.
Qed.

Lemma vad_store : forall regs1 mem1 md1, vad_STc regs1 mem1 md1 ->
SRr SEGS W (mkCfg (mkst regs1 (Z_to_bv 64 (BASE + VAD_ST)) mem1 (seg_rom SEGS)) md1) vad_Q.
Proof using vad_all.
intros regs1 mem1 md1 (HCE & LT & HEX & R8 & R9 & R24 & R10 & HK2 & (f16 & L16 & HF16 & HENC)).
pose proof HCE as (HJ & HFR & R2 & R3 & R4).
pose proof vad_sp as (Hal16 & Hslo & Hshi & _). pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof vad_tab_facts as (T1 & T2 & T3 & T4 & T5 & T6). pose proof vad_n_facts as (N1 & N2 & N3 & N4 & N5 & N6 & N7).
pose proof HADD as ((_ & _ & HRT & _ & (b & m & Hbm & Hb1 & Hb2) & HTA & _ & _ & _ & HNV & _ & _ & HDJ) & _ & _ & _ & _ & _ & _ & _ & Hvid).
assert (HST : STK_reac_declared_vlan_add = 8304) by reflexivity.
destruct HRT as (bt & HBT & HET).
unfold sa_disj, seg_spec.RVLAN_SIZE in HDJ, Hb2.
set (D := tab + 18 * L) in *.
assert (HKP : forall x, (0 <= x < 2 ^ 64 /\ ~ (sp0 - STK_reac_declared_vlan_add <= x < sp0) /\ ~ (D <= x < D + 18)) -> rdW W mem1 x = rdW W mem x)
  by (intros x (Hx1 & Hx2 & Hx3); exact (HK2 x Hx1 Hx2 Hx3)).
assert (VN1 : sa_val (rdW W mem1) n 4 L) by (apply (vad_sa_val_keep _ _ _ _ _ _ HKP HNV); intros i Hi; cbv beta; lia).
assert (PN : forall a, n <= a < n + 4 -> apresent (w_H W) mem1 a).
{ intros a Ha. apply (apresent_of_aview SEGS); [lia | |].
  - intros Hi. pose proof (pa_img_range _ Hi) as HR. unfold kImgEnd in HR. lia.
  - replace a with (n + Z.of_nat (Z.to_nat (a - n))) by lia. rewrite (VN1 (Z.to_nat (a - n)) ltac:(lia)). discriminate. }
assert (RA1 : range_addressable (rdW W mem1) SHADOW_OFF (D + 16) 2).
{ apply (vad_ra_keep (rdW W mem) _ _ _ _ HKP).
  - destruct HTA as (_ & _ & _ & HRA & _). apply (range_addressable_sub _ _ tab (seg_spec.RVLAN_SIZE * max)); [exact HRA | lia | unfold seg_spec.RVLAN_SIZE; lia].
  - intros x Hx. cbv beta. rewrite <- SB_SHADOW_OFF. unfold shadow_of_addr.
    assert (0 <= x / 8 < 2 ^ 44) by (split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]).
    split; [unfold SB; lia|]. split; [unfold SB; lia|].
    intros Hin. apply (T5 (SB + x / 8)); [lia | lia]. }
destruct (al_blocks _ _ LAWS ly S W mem1 md1 b m (proj1 HJ) Hbm) as (_ & _ & _ & _ & Hppres & _).
pose proof (req_size_pos0 m ltac:(lia)) as [_ Hreq].
assert (PD1 : forall a, D + 16 <= a < D + 18 -> apresent (w_H W) mem1 a) by (intros a Ha; exact (proj1 (Hppres a ltac:(lia)))).
assert (RAN1 : range_addressable (rdW W mem1) SHADOW_OFF n 4).
{ apply (vad_ra_keep (rdW W mem) _ _ _ _ HKP).
  - pose proof HADD as ((_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & (_ & _ & _ & HRAn & _) & _) & _). exact HRAn.
  - intros x Hx. cbv beta. rewrite <- SB_SHADOW_OFF. unfold shadow_of_addr.
    assert (0 <= x / 8 < 2 ^ 44) by (split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]).
    split; [unfold SB; lia|]. split; [unfold SB; lia|].
    intros Hin. apply (T5 (SB + x / 8)); [lia | lia]. }
destruct (vad_st_seed regs1 mem1 LT R2 R8 R24 R10 VN1 RA1 RAN1 PD1 PN) as [HS SHOK]. fold D in HS, SHOK.
assert (HEI : img_env VAL A_LIM (Eimg (Ereg regs1 (map w64 [SB; n; L; D])))) by apply Eimg_env.
assert (EE : forall k (r : bv 5), Z.of_nat k = bv_unsigned r -> ew (Eimg (Ereg regs1 (map w64 [SB; n; L; D]))) k = getr regs1 r)
  by (intros k r Hk; apply ew_Eimg_Ereg_nat; exact Hk).
pose proof (vad_ex_w64 regs1 [SB; n; L; D] 0 ltac:(unfold A_TEXT; lia) ltac:(cbn; lia)) as E32.
pose proof (vad_ex_w64 regs1 [SB; n; L; D] 1 ltac:(unfold A_TEXT; lia) ltac:(cbn; lia)) as E33.
pose proof (vad_ex_w64 regs1 [SB; n; L; D] 2 ltac:(unfold A_TEXT; lia) ltac:(cbn; lia)) as E34.
pose proof (vad_ex_w64 regs1 [SB; n; L; D] 3 ltac:(unfold A_TEXT; lia) ltac:(cbn; lia)) as E35.
cbn [nth Nat.add] in E32, E33, E34, E35.
remember (Eimg (Ereg regs1 (map w64 [SB; n; L; D]))) as E eqn:HE. clear HE.
assert (Usp : bv_unsigned (ew E 2) = sp0 - 112) by (rewrite (EE 2%nat 2%bv eq_refl), R2; apply unsigned_lit_small; lia).
assert (E33u : bv_unsigned (ew E 33) = n) by (rewrite E33; apply unsigned_lit_small; lia).
assert (E34u : bv_unsigned (ew E 34) = L) by (rewrite E34; apply unsigned_lit_small; lia).
assert (E35u : bv_unsigned (ew E 35) = D) by (rewrite E35; apply unsigned_lit_small; lia).
paj_run_to_tok RUNTO HS HJ SHOK Bspan VAD_EPI.
{ lazymatch goal with |- awr_ok _ _ ?Ex ?rs ?stk ?spx ?fp ?b0 ?bc ?fr0 ?lyx ?own => let rs' := eval vm_compute in rs in change (awr_ok SEGS B Ex rs' stk spx fp b0 bc fr0 lyx own) end.
  eapply awr_ok_cons_gen with (n := 35%nat) (b := D); [reflexivity | exact E35u | intros a Ha; cbn [YP09.r_wlo YP09.r_whi] in Ha; apply vad_awr_tab; [exact HEX | exact LT | lia] |].
  eapply awr_ok_cons_gen with (n := 33%nat) (b := n); [reflexivity | exact E33u | intros a Ha; cbn [YP09.r_wlo YP09.r_whi] in Ha; apply vad_awr_n; [exact HEX | exact LT | lia] |].
  apply awr_ok_nil. }
vad_md.
(* what the run wrote: the vid at D + 16 and the new count at n; nothing else *)
lazymatch type of HS with st_ok_pi _ _ ?Ex ?ssx (restrict _ ?msx) =>
  let r0 := eval vm_compute in (nth 0 (ss_mem ssx) (stack_region 0)) in
  let r1 := eval vm_compute in (nth 1 (ss_mem ssx) (stack_region 0)) in
  pose proof (st_ok_pi_region_nth Ex ssx (restrict _ msx) 0 r0 HS ltac:(vm_compute; reflexivity)) as HR0;
  pose proof (st_ok_pi_region_nth Ex ssx (restrict _ msx) 1 r1 HS ltac:(vm_compute; reflexivity)) as HR1;
  cbn [ms_mem restrict] in HR0, HR1;
  assert (Ux35 : bv_unsigned (ew Ex 35) = D) by (cbn [ew ewset Nat.eqb]; exact E35u);
  assert (Ux33 : bv_unsigned (ew Ex 33) = n) by (cbn [ew ewset Nat.eqb]; exact E33u);
  assert (Dv : sv_denot Ex (SOff 9 0) = Z_to_bv 64 vid)
    by (cbn [sv_denot ew ewset Nat.eqb]; rewrite (EE 9%nat 9%bv eq_refl), R9, Z.add_0_r; unfold w64; apply Z_to_bv_bv_unsigned);
  assert (Dn : sv_denot Ex (SOff 34 1) = Z_to_bv 64 (L + 1))
    by (cbn [sv_denot ew ewset Nat.eqb]; rewrite E34u; reflexivity) end.
pose proof (field_of_region _ _ 35 D _ 0 18 16 18 16 2 (SOff 9 0) vid HR0 Ux35 ltac:(cbn; tauto) Dv ltac:(cbn; lia) ltac:(cbn; lia)) as VVID.
pose proof (field_of_region _ _ 33 n _ 0 4 0 4 0 4 (SOff 34 1) (L + 1) HR1 Ux33 ltac:(cbn; tauto) Dn ltac:(cbn; lia) ltac:(cbn; lia)) as VCNT.
change (N.to_nat 2) with 2%nat in VVID. change (N.to_nat 4) with 4%nat in VCNT. rewrite Z.add_0_r in VCNT.
pose proof (vad_sa_of_val_mem _ _ _ _ _ _ VVID) as SVID. pose proof (vad_sa_of_val_mem _ _ _ _ _ _ VCNT) as SCNT.
lazymatch type of HFr with frame_of ?Ex _ (mrestrict ?H ?m1) (mrestrict ?H ?m2) =>
  assert (KF : forall x, (0 <= x < 2 ^ 64 /\ ~ (D + 16 <= x < D + 18) /\ ~ (n <= x < n + 4)) -> aview SEGS H m2 x = aview SEGS H m1 x)
  by (intros x0 (Hx0 & Hn1 & Hn2); apply (kept_of_frame (segs := SEGS) _ _ _ _ _ (fun x => (D + 16 <= x < D + 18) \/ (n <= x < n + 4)) HFr);
      [ intros b0 wlo whi a0 Hin Hrr; vm_compute in Hin;
        repeat (destruct Hin as [Hq | Hin]; [injection Hq as <- <- <-; cbn [base_val ew ewset Nat.eqb] in Hrr; rewrite ?E35u, ?E33u in Hrr; lia|]); destruct Hin
      | exact Hx0 | tauto ]) end.
clear HF HFr HG.
pmkst HS.
prreg HS (2%bv : bv 5) F2. prreg HS (3%bv : bv 5) F3. prreg HS (4%bv : bv 5) F4. prreg HS (20%bv : bv 5) F20.
pose proof (vad_vlan_add_app t max p vid HEX LT) as EVA.
assert (HKF : forall x, (0 <= x < 2 ^ 64 /\ ~ (sp0 - STK_reac_declared_vlan_add <= x < sp0) /\ ~ (D <= x < D + 18) /\ ~ (n <= x < n + 4)) ->
  rdW W (ms_mem ms) x = rdW W mem x).
{ intros x (H1 & H2 & H3 & H4). rewrite (KF x ltac:(split; [exact H1|]; split; [lia | exact H4])). exact (HKP x (conj H1 (conj H2 H3))). }
apply (vad_epi 1); rewrite ?EVA; cbn [fst snd].
- split; [exact HJ|]. split.
  + intros j r Hr. assert (Hj : (j < 13)%nat) by (change 13%nat with (length vad_saved); apply (proj1 (nth_error_Some vad_saved j)); rewrite Hr; discriminate).
    apply (vad_sa_val_keep (rdW W mem1) _ (fun x => 0 <= x < 2 ^ 64 /\ ~ (D + 16 <= x < D + 18) /\ ~ (n <= x < n + 4)) _ _ _ KF (HFR j r Hr)).
    intros k Hk. cbv beta. lia.
  + split; [rewrite F2, (EE 2%nat 2%bv eq_refl); exact R2|].
    split; [rewrite F3, (EE 3%nat 3%bv eq_refl); exact R3 | rewrite F4, (EE 4%nat 4%bv eq_refl); exact R4].
- rewrite F20. reflexivity.
- reflexivity.
- exists (bt ++ (f16 ++ Mem.le2 (Z_to_bv 64 vid))). split.
  + apply vad_sa_bytes_app. split.
    * apply (vad_sa_bytes_keep _ _ _ _ _ HKF HBT). intros i Hi. destruct HET as [HL _]. cbv beta. lia.
    * destruct HET as [HL _]. rewrite HL. replace (tab + Z.of_nat (18 * length t)) with D by lia.
      apply vad_sa_bytes_app. split.
      -- apply (vad_sa_bytes_keep (rdW W mem1) _ (fun x => 0 <= x < 2 ^ 64 /\ ~ (D + 16 <= x < D + 18) /\ ~ (n <= x < n + 4)) _ _ KF HF16).
         intros i Hi. cbv beta. lia.
      -- rewrite L16. replace (D + Z.of_nat 16) with (D + 16) by lia.
         intros i Hi. rewrite Mem.length_le2 in Hi. rewrite (SVID i Hi). f_equal. unfold le_byte. symmetry. apply vad_le2_byte; [lia | exact Hi].
  + apply vad_rtab_enc_snoc; [exact HET | exact HENC].
- rewrite length_app. cbn [length]. replace (Z.of_nat (length t + 1)) with (L + 1) by lia. exact SCNT.
- intros HG. apply (vad_sa_bytes_keep _ _ _ _ _ HKF HG). intros i Hi. cbv beta.
  unfold seg_spec.GUARD_BYTES in Hi. rewrite repeat_length in Hi. unfold seg_spec.RVLAN_SIZE. lia.
- intros a Ha Hw He. apply HKF. split; [exact Ha|]. split; [exact Hw|].
  unfold vtab_E, seg_spec.RVLAN_SIZE in He. rewrite length_app in He. cbn [length] in He.
  replace (length t <? length t + 1)%nat with true in He by (symmetry; apply Nat.ltb_lt; lia).
  split; intros Hin; apply He; [left; lia | right; exact Hin].
Qed.

(* ---------- the search body's facts at a cut ---------- *)
(* the memory below the window: a sa_addr range keeps its shadow facts *)
Lemma vad_sa_addr_keep : forall (rd rd' : reader) q len,
(forall y, 0 <= y < 2 ^ 64 -> ~ (sp0 - STK_reac_declared_vlan_add <= y < sp0) -> rd' y = rd y) ->
q + len <= 2 ^ 47 -> sa_addr rd q len -> sa_addr rd' q len.
Proof using vad_all.
intros rd rd' q len HK Hq (H0 & H1 & H2 & H3 & H4).
pose proof vad_sp as (Hal16 & Hslo & Hshi & _). pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (HST : STK_reac_declared_vlan_add = 8304) by reflexivity.
assert (HKP : forall y, (0 <= y < 2 ^ 64 /\ ~ (sp0 - STK_reac_declared_vlan_add <= y < sp0)) -> rd' y = rd y) by (intros y [Hy1 Hy2]; exact (HK y Hy1 Hy2)).
split; [exact H0|]. split; [exact H1|]. split; [exact H2|]. split.
- apply (vad_ra_keep rd rd' _ q len HKP H3). intros x Hx. cbv beta. rewrite <- SB_SHADOW_OFF. unfold shadow_of_addr.
  assert (0 <= x / 8 < 2 ^ 44) by (split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]). unfold SB. lia.
- intros Hn. apply (vad_hull_keep rd rd' _ q len HKP (H4 Hn)). intros s Hs. cbv beta.
  unfold shadow_addr in Hs. rewrite <- SB_SHADOW_OFF in Hs.
  assert (0 <= q / 8 < 2 ^ 44) by (split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]).
  assert (0 <= (q + len - 1) / 8 < 2 ^ 44) by (split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]).
  unfold SB in *. Z.div_mod_to_equations. lia.
Qed.
(* the parent: where it lies, its bytes as a byte list *)
Lemma vad_par_facts : 0 < par /\
par + Z.of_nat (length p) - (par + Z.of_nat (length p)) mod 8 + 8 <= alloc_ceiling /\
par + Z.of_nat (length p) + 1 <= alloc_ceiling.
Proof using vad_all.
pose proof HPRE as (HAR & _). pose proof vad_sp as (Hal16 & Hslo & Hshi & HAC4).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof HADD as (_ & Hp0 & HSTR & HPA & HPL & HPM & HLOC & _).
destruct HPA as (P0 & P1 & _).
assert (Hend : par + Z.of_nat (length p) < alloc_ceiling).
{ destruct HLOC as [(b & m & Hbm & Hb1 & Hb2) | [(cid & pos & Hin & Hcid & Hf1 & Hf2) | HIMG]].
  - destruct (al_blocks _ _ LAWS ly S W mem md b m HAR Hbm) as (_ & _ & Hpceil & _).
    pose proof (req_size_pos0 m ltac:(lia)) as [_ Hreq]. lia.
  - destruct (frames_bounds SEGS B LAWS ly S W mem md cid pos HAR Hin) as (_ & Hfc & _). lia.
  - destruct (HIMG (par + Z.of_nat (length p)) ltac:(lia)) as (Himg & _). pose proof (pa_img_range _ Himg) as HR.
    unfold kImgEnd in HR. lia. }
assert (Hr0 : 0 <= par + Z.of_nat (length p) < alloc_ceiling) by (split; [lia | exact Hend]).
pose proof (tail_below (par + Z.of_nat (length p)) alloc_ceiling Hr0 HAC4) as HT.
repeat split; lia.
Qed.
Lemma vad_par_bytes : exists pb : list byte,
seg_spec.zs pb = p /\ ~ In (Z_to_bv 8 0) pb /\ length pb = length p /\ astr_atR (rdW W mem) par pb.
Proof using vad_all.
pose proof HADD as (_ & _ & ((HZ & HN0) & _) & _).
exists (map (Z_to_bv 8) p).
assert (Hr : forall k, (k < length p)%nat -> 0 <= nth k p 0 < 256).
{ intros k Hk. pose proof (HZ k ltac:(rewrite length_app; cbn [length]; lia)) as Hb.
  rewrite app_nth1 in Hb by exact Hk. destruct (aview_byte SEGS _ _ _ _ Hb) as (b & _ & Hbv & Hrange). lia. }
assert (Hzs : seg_spec.zs (map (Z_to_bv 8) p) = p).
{ unfold seg_spec.zs. rewrite map_map. rewrite <- (map_id p) at 2. apply map_ext_in. intros z Hz.
  apply In_nth with (d := 0) in Hz as (k & Hk & <-). rewrite Z_to_bv_unsigned. unfold bv_wrap.
  change (bv_modulus 8) with 256. apply Z.mod_small. exact (Hr k Hk). }
split; [exact Hzs|]. split.
{ intros Hin. apply HN0. rewrite <- Hzs. change 0 with (bv_unsigned (Z_to_bv 8 0)). unfold seg_spec.zs. apply in_map. exact Hin. }
split; [apply length_map|].
split; [|intros Hin; apply HN0; rewrite <- Hzs; change 0 with (bv_unsigned (Z_to_bv 8 0)); unfold seg_spec.zs; apply in_map; exact Hin].
intros k Hk. rewrite length_app, length_map in Hk. cbn [length] in Hk.
rewrite (HZ k ltac:(rewrite length_app; cbn [length]; lia)). f_equal.
destruct (Nat.lt_ge_cases k (length p)) as [Hlt|Hge].
- rewrite app_nth1 by exact Hlt. rewrite app_nth1 by (rewrite length_map; exact Hlt).
  rewrite map_nth. rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 8) with 256.
  symmetry. apply Z.mod_small. exact (Hr k Hlt).
- assert (k = length p) by lia. subst k. rewrite app_nth2 by lia. rewrite app_nth2 by (rewrite length_map; lia).
  rewrite length_map, Nat.sub_diag. reflexivity.
Qed.
(* entry i of the table, at a state whose memory agrees with the entry's below the window *)
Lemma vad_entry_at : forall (i : nat) mem1, (i < length t)%nat ->
(forall y, 0 <= y < 2 ^ 64 -> ~ (sp0 - STK_reac_declared_vlan_add <= y < sp0) -> rdW W mem1 y = rdW W mem y) ->
exists sx : list byte, seg_spec.zs sx = fst (nth i t ([], 0)) /\ ~ In (Z_to_bv 8 0) sx /\ (length sx < 16)%nat /\
astr_atR (rdW W mem1) (tab + 18 * Z.of_nat i) sx /\
sa_val (rdW W mem1) (tab + 18 * Z.of_nat i + 16) 2 (snd (nth i t ([], 0))) /\
0 <= snd (nth i t ([], 0)) < 65536.
Proof using vad_all.
intros i mem1 Hi HK.
pose proof vad_sp as (Hal16 & Hslo & Hshi & _). pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof vad_tab_facts as (T1 & T2 & T3 & _). assert (HST : STK_reac_declared_vlan_add = 8304) by reflexivity.
pose proof HADD as ((_ & _ & (bt & HBT & HET) & _) & _).
destruct (vad_entry_fields t bt i HET Hi) as (sx & Zsx & Hn0 & Lsx & Hby & Hv & Hvb & Hlen).
exists sx. split; [exact Zsx|]. split; [exact Hn0|]. split; [exact Lsx|]. split.
- split; [|exact Hn0]. intros k Hk. rewrite length_app in Hk. cbn [length] in Hk.
  rewrite HK by (pose proof HET as [HL _]; lia).
  replace (tab + 18 * Z.of_nat i + Z.of_nat k) with (tab + Z.of_nat (18 * i + k)) by lia.
  rewrite (HBT (18 * i + k)%nat ltac:(lia)). rewrite Hby by lia. reflexivity.
- split; [|exact Hv]. intros k Hk.
  rewrite HK by (pose proof HET as [HL _]; lia).
  replace (tab + 18 * Z.of_nat i + 16 + Z.of_nat k) with (tab + Z.of_nat (18 * i + 16 + k)) by lia.
  rewrite (HBT (18 * i + 16 + k)%nat ltac:(lia)). rewrite Hvb by lia. f_equal.
  unfold le_byte. apply vad_le2_byte; [exact Hv | exact Hk].
Qed.

Lemma vad_amem_sub : forall q len q' len', amem_range q len -> q <= q' -> q' + len' <= q + len -> 0 <= q' -> amem_range q' len'.
Proof using. intros q len q' len' H H1 H2 H3. unfold amem_range in *. lia. Qed.
Lemma vad_hull_sub : forall rd q len q' len', shadow_hull_vis rd q len -> q <= q' -> q' + len' <= q + len -> 0 < len' ->
shadow_hull_vis rd q' len'.
Proof using.
intros rd q len q' len' H H1 H2 H3 s Hs. apply H. unfold shadow_addr in *.
assert (q / 8 <= q' / 8) by (apply Z.div_le_mono; lia).
assert ((q' + len' - 1) / 8 <= (q + len - 1) / 8) by (apply Z.div_le_mono; lia).
Z.div_mod_to_equations. lia.
Qed.
(* the parent string at a strcmp / strncpy call: a state whose memory agrees with the entry's on a set P that holds
   the parent's bytes, its word tail and the shadow band *)
Lemma vad_par_call : forall pb regsc memc (P : Z -> Prop), seg_spec.zs pb = p -> ~ In (Z_to_bv 8 0) pb -> length pb = length p ->
astr_atR (rdW W mem) par pb ->
(forall y, P y -> rdW W memc y = rdW W mem y) ->
(forall y, par <= y < par + Z.of_nat (length p) - (par + Z.of_nat (length p)) mod 8 + 8 -> P y) ->
(forall y, SB <= y < SB + 2 ^ 44 - 8 -> P y) ->
alloc_ceiling <= spZ regsc - 2 * ESTACK ->
astr_at SEGS W memc par pb /\ aread_ok SEGS (2 * ESTACK) W regsc memc par (astr_len pb + 1) /\
atail_vis SEGS W memc (par + astr_len pb) /\ amem_range par (astr_len pb + 8).
Proof using vad_all.
intros pb regsc memc P Zpb Hpb0 Lpb STRp HK HPb HPs Hsc.
pose proof vad_sp as (Hal16 & Hslo & Hshi & HAC4). pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof vad_par_facts as (Pp0 & Pp1 & Pp2).
pose proof HADD as (_ & Hpz & (_ & HTL) & HPA & HPL & HPM & _).
assert (HST : STK_reac_declared_vlan_add = 8304) by reflexivity.
pose proof (Z.mod_pos_bound (par + Z.of_nat (length p)) 8 ltac:(lia)) as Hm8.
unfold astr_len. rewrite Lpb.
assert (STRc : astr_atR (rdW W memc) par pb).
{ destruct STRp as [Hb Hn]. split; [|exact Hn]. intros i Hi. rewrite length_app, Lpb in Hi. cbn [length] in Hi.
  rewrite (HK (par + Z.of_nat i)) by (apply HPb; lia). apply Hb. rewrite length_app, Lpb. cbn [length]. lia. }
split; [apply (astr_atR_view SEGS); exact STRc|].
destruct HPA as (A0 & A1 & A2 & A3 & A4).
split.
- split; [exact A0|]. split; [exact A1|]. split; [lia|]. split.
  + intros a Ha. split.
    * destruct STRc as [Hb _]. replace a with (par + Z.of_nat (Z.to_nat (a - par))) by lia.
      rewrite Hb; [discriminate|]. rewrite length_app, Lpb. cbn [length]. lia.
    * unfold ascratch_stk. lia.
  + split; [exact A2|]. split.
    * apply (vad_ra_keep (rdW W mem) _ P _ _ HK A3). intros x Hx. apply HPs. rewrite <- SB_SHADOW_OFF. unfold shadow_of_addr.
      assert (0 <= x / 8 <= 0x7fffff800000 / 8) by (split; [apply Z.div_pos; lia | apply Z.div_le_mono; lia]). lia.
    * intros Hn. apply (vad_hull_keep (rdW W mem) _ P _ _ HK (A4 Hn)). intros y Hy. apply HPs.
      unfold shadow_addr in Hy. rewrite <- SB_SHADOW_OFF in Hy.
      assert (0 <= par / 8 < 2 ^ 44) by (split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]).
      assert (0 <= (par + (Z.of_nat (length p) + 1) - 1) / 8 <= 0x7fffff800000 / 8) by (split; [apply Z.div_pos; lia | apply Z.div_le_mono; lia]).
      unfold SB in *. Z.div_mod_to_equations. lia.
- split.
  + intros a Ha. rewrite (HK a) by (apply HPb; lia). exact (HTL a Ha).
  + exact HPM.
Qed.
(* entry i's parent string at a strcmp call *)
Lemma vad_ent_call : forall (i : nat) sx regsc memc mdc, (i < length t)%nat -> (length sx < 16)%nat ->
astr_atR (rdW W memc) (tab + 18 * Z.of_nat i) sx -> AR SEGS B ly S W memc mdc ->
alloc_ceiling <= spZ regsc - 2 * ESTACK ->
astr_at SEGS W memc (tab + 18 * Z.of_nat i) sx /\
aread_ok SEGS (2 * ESTACK) W regsc memc (tab + 18 * Z.of_nat i) (astr_len sx + 1) /\
atail_vis SEGS W memc (tab + 18 * Z.of_nat i + astr_len sx).
Proof using vad_all.
intros i sx regsc memc mdc Hi Lsx STRx HAR1 Hsc.
pose proof vad_tab_facts as (T1 & T2 & T3 & T4 & T5 & T6). pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof HADD as ((_ & _ & _ & _ & (b & m & Hbm & Hb1 & Hb2) & _) & _). unfold seg_spec.RVLAN_SIZE in Hb2.
destruct (al_blocks _ _ LAWS ly S W memc mdc b m HAR1 Hbm) as (_ & _ & _ & _ & Hppres & _).
pose proof (req_size_pos0 m ltac:(lia)) as [_ Hreq].
unfold astr_len.
split; [apply (astr_atR_view SEGS); exact STRx|].
split.
- apply (aread_ok_of_block SEGS B LAWS (2 * ESTACK) ly S W regsc memc mdc b m); [exact HAR1 | exact Hbm | lia | lia | lia | exact Hsc].
- intros a Ha. apply (aview_some_of_apresent SEGS). apply (proj1 (Hppres a ltac:(Z.div_mod_to_equations; lia))).
Qed.
(* the read-only bytes the wrappers read, at a state whose memory agrees with the entry's on the image *)
Lemma vad_rom_at : forall memc (P : Z -> Prop), (forall y, P y -> rdW W memc y = rdW W mem y) ->
(forall y, 0x10000 <= y < kImgEnd -> P y) ->
rt_rom_view SEGS B W memc.
Proof using vad_all.
intros memc P HK HP x Hx Ho He.
destruct Hx as (sg & Hsg & Hw & Hr).
assert (Himg : in_img SEGS x) by (exists sg; split; [exact Hsg | exact Hr]).
pose proof (pa_img_range _ Himg) as HR. rewrite (HK x) by (apply HP; exact HR).
apply HROD; [left; exists sg; split; [exact Hsg | split; [exact Hw | exact Hr]] | exact Ho | exact He].
Qed.
(* a read range shrinks *)
Lemma vad_aread_sub : forall stk regsc memc x k k', aread_ok SEGS stk W regsc memc x k -> 0 <= k' <= k ->
aread_ok SEGS stk W regsc memc x k'.
Proof using.
intros stk regsc memc x k k' (H0 & H1 & H2 & H3 & H4 & H5 & H6) Hk.
split; [exact H0|]. split; [lia|]. split; [lia|]. split; [intros a Ha; apply H3; lia|].
split; [apply (vad_amem_sub x k); [exact H4 | lia | lia | lia]|].
split; [apply (range_addressable_sub _ _ x k); [exact H5 | lia | lia]|].
intros Hk'. apply (vad_hull_sub _ x k); [apply H6; lia | lia | lia | lia].
Qed.

(* ---------- the search body: 0x89ed8 .. the latch or the epilogue, the strcmp call at 0x89ef8 ---------- *)
Lemma vad_step : forall i regs1 mem1 md1, vad_LHc i regs1 mem1 md1 ->
(forall r m d, vad_LTc i r m d -> SRr SEGS W (mkCfg (mkst r (Z_to_bv 64 (BASE + VAD_LT)) m (seg_rom SEGS)) d) vad_Q) ->
SRr SEGS W (mkCfg (mkst regs1 (Z_to_bv 64 (BASE + VAD_LH)) mem1 (seg_rom SEGS)) md1) vad_Q.
Proof using vad_allc.
intros i regs1 mem1 md1 (HCUT & (R8 & R9 & R18 & R19 & R20 & R21 & R24 & R25 & R26) & Hi & HEX & R23 & R22 & R27) KLT.
pose proof HCUT as ((HJ & HFR & R2 & R3 & R4) & HK).
pose proof HPRE as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof vad_sp as (Hal16 & Hslo & Hshi & HAC4). pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof vad_tab_facts as (T1 & T2 & T3 & T4 & T5 & T6). pose proof vad_par_facts as (Pp0 & Pp1 & Pp2).
pose proof HADD as ((_ & _ & _ & _ & (bk & mk & Hbm & Hb1 & Hb2) & HTA & _) & Hpz & HSTR & HPA & HPL & HPM & HLOC & HPDJ & Hvid).
assert (HST : STK_reac_declared_vlan_add = 8304) by reflexivity. assert (Hes : ESTACK = 4096) by reflexivity.
unfold seg_spec.RVLAN_SIZE in *.
assert (HKY : forall y, 0 <= y < 2 ^ 64 -> ~ (sp0 - STK_reac_declared_vlan_add <= y < sp0) -> rdW W mem1 y = rdW W mem y)
  by (intros y Hy1 Hy2; exact (HK y Hy1 Hy2)).
destruct (vad_entry_at i mem1 Hi HKY) as (sx & Zsx & Hsx0 & Lsx & STRx & VV & Hvi).
set (e := nth i t ([], 0)) in *. set (vi := snd e) in *.
set (Q := tab + 18 * Z.of_nat i) in *.
assert (RAQ : range_addressable (rdW W mem1) SHADOW_OFF Q 18).
{ apply (vad_ra_keep (rdW W mem) _ (fun y => 0 <= y < 2 ^ 64 /\ ~ (sp0 - STK_reac_declared_vlan_add <= y < sp0))); [intros y [Hy1 Hy2]; exact (HKY y Hy1 Hy2)| |].
  - destruct HTA as (_ & _ & _ & HRA & _). apply (range_addressable_sub _ _ tab (18 * max)); [exact HRA | lia | lia].
  - intros x Hx. cbv beta. rewrite <- SB_SHADOW_OFF. unfold shadow_of_addr.
    assert (0 <= x / 8 < 2 ^ 44) by (split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]). unfold SB. lia. }
destruct (vad_lh_seed i vi regs1 mem1 Hi Hvi R2 R24 R23 R22 VV RAQ) as [HS SHOK]. fold Q in HS, SHOK.
assert (HEI : img_env VAL A_LIM (Eimg (Ereg regs1 (map w64 [SB; Q; vi])))) by apply Eimg_env.
assert (EE : forall k (r : bv 5), Z.of_nat k = bv_unsigned r -> ew (Eimg (Ereg regs1 (map w64 [SB; Q; vi]))) k = getr regs1 r)
  by (intros k r Hk; apply ew_Eimg_Ereg_nat; exact Hk).
pose proof (vad_ex_w64 regs1 [SB; Q; vi] 0 ltac:(unfold A_TEXT; lia) ltac:(cbn; lia)) as E32.
pose proof (vad_ex_w64 regs1 [SB; Q; vi] 1 ltac:(unfold A_TEXT; lia) ltac:(cbn; lia)) as E33.
pose proof (vad_ex_w64 regs1 [SB; Q; vi] 2 ltac:(unfold A_TEXT; lia) ltac:(cbn; lia)) as E34.
cbn [nth Nat.add] in E32, E33, E34.
remember (Eimg (Ereg regs1 (map w64 [SB; Q; vi]))) as E eqn:HE. clear HE.
assert (Usp : bv_unsigned (ew E 2) = sp0 - 112) by (rewrite (EE 2%nat 2%bv eq_refl), R2; apply unsigned_lit_small; lia).
assert (E33u : bv_unsigned (ew E 33) = Q) by (rewrite E33; apply unsigned_lit_small; lia).
assert (E34u : bv_unsigned (ew E 34) = vi) by (rewrite E34; apply unsigned_lit_small; lia).
assert (U9 : U E (SOff 9 0) = vid) by (apply U_atom; [rewrite (EE 9%nat 9%bv eq_refl); exact R9 | lia]).
(* 0x89ed8 .. 0x89eec: inline check 2, the vid field, bne *)
paj_run_tok RUN HS HJ SHOK Bspan.
{ awr_ok_tac; exact Usp. }
vad_md.
vad_keep_empty HFr KEEP1. clear HF HFr HG.
lazymatch goal with HS0 : st_ok_pi _ _ ?Ex _ _ |- _ =>
  assert (U34x : U Ex (SOff 34 0) = vi) by (apply U_atom; [cbn [ew ewset Nat.eqb]; exact E34 | lia]);
  assert (U9x : U Ex (SOff 9 0) = vid) by (apply U_atom; [cbn [ew ewset Nat.eqb]; rewrite (EE 9%nat 9%bv eq_refl); exact R9 | lia]);
  assert (EEx : forall k (rr : bv 5), Z.of_nat k = bv_unsigned rr -> ew Ex k = getr regs1 rr)
    by (intros k rr Hk; pose proof (bv_unsigned_in_range 5 rr) as Hrr; change (bv_modulus 5) with 32 in Hrr;
        cbn [ew ewset]; repeat (rewrite (proj2 (Nat.eqb_neq _ _)) by lia); apply EE; exact Hk) end.
assert (HKY1 : forall y, 0 <= y < 2 ^ 64 -> ~ (sp0 - STK_reac_declared_vlan_add <= y < sp0) -> rdW W (ms_mem ms) y = rdW W mem y)
  by (intros y Hy1 Hy2; rewrite (KEEP1 y Hy1); exact (HKY y Hy1 Hy2)).
psrr_branch_tok RUN BR HS SHOK Bspan.
- (* tab[i].vid <> vid: the latch *)
  assert (HNE : vi <> vid) by (rewrite branch_ne_U, U34x, U9x in Hc; apply negb_true_iff, Z.eqb_neq in Hc; exact Hc).
  paj_run_to_tok RUNTO HS HJ SHOK Bspan VAD_LT.
  { awr_ok_tac; cbn [ew ewset Nat.eqb]; exact Usp. }
  vad_md.
  vad_keep_empty HFr KEEP2. clear HF HFr HG.
  pmkst HS.
  prreg HS (2%bv : bv 5) P2. prreg HS (3%bv : bv 5) P3. prreg HS (4%bv : bv 5) P4.
  prreg HS (8%bv : bv 5) P8. prreg HS (9%bv : bv 5) P9. prreg HS (18%bv : bv 5) P18. prreg HS (19%bv : bv 5) P19.
  prreg HS (20%bv : bv 5) P20. prreg HS (21%bv : bv 5) P21. prreg HS (22%bv : bv 5) P22. prreg HS (23%bv : bv 5) P23.
  prreg HS (24%bv : bv 5) P24. prreg HS (25%bv : bv 5) P25. prreg HS (26%bv : bv 5) P26. prreg HS (27%bv : bv 5) P27.
  apply KLT. split; [|split; [|split; [exact Hi|]]].
  + apply (vad_cut_kept regs1 mem1 md1 _ _ _ (sp0 - STK_reac_declared_vlan_add) (sp0 - STK_reac_declared_vlan_add) HCUT HJ); [| lia | lia
      | rewrite P2; apply EE; reflexivity | rewrite P3; apply EE; reflexivity | rewrite P4; apply EE; reflexivity].
    intros x Hx _. rewrite (KEEP2 x Hx). exact (KEEP1 x Hx).
  + split; [rewrite P8; rewrite (EE 8%nat 8%bv eq_refl); exact R8|].
    split; [rewrite P9; rewrite (EE 9%nat 9%bv eq_refl); exact R9|].
    split; [rewrite P18; rewrite (EE 18%nat 18%bv eq_refl); exact R18|].
    split; [rewrite P19; rewrite (EE 19%nat 19%bv eq_refl); exact R19|].
    split; [rewrite P20; rewrite (EE 20%nat 20%bv eq_refl); exact R20|].
    split; [rewrite P21; rewrite (EE 21%nat 21%bv eq_refl); exact R21|].
    split; [rewrite P24; exact E32|].
    split; [rewrite P25; rewrite (EE 25%nat 25%bv eq_refl); exact R25|].
    rewrite P26; rewrite (EE 26%nat 26%bv eq_refl); exact R26.
  + split.
    { rewrite HEX, (vad_existsb_skipn_S (vad_match vid p) t i ([], 0) Hi). fold e.
      unfold vad_match at 1. fold vi. rewrite (proj2 (Z.eqb_neq _ _) HNE). reflexivity. }
    split; [rewrite P23, E33; reflexivity|].
    split; [rewrite P22, E33u; reflexivity|].
    rewrite P27, (EE 27%nat 27%bv eq_refl); exact R27.
- (* tab[i].vid = vid: strcmp(tab[i].parent, parent) *)
  assert (HEQ : vi = vid) by (rewrite branch_ne_U, U34x, U9x in Hc; apply negb_false_iff, Z.eqb_eq in Hc; exact Hc).
  clear Hc.
  paj_run_tok RUN HS HJ SHOK Bspan.
  { awr_ok_tac; cbn [ew ewset Nat.eqb]; exact Usp. }
  vad_md.
  vad_keep_empty HFr KEEP2. clear HF HFr HG.
  pmkst HS.
  prreg HS (1%bv : bv 5) P1. prreg HS (2%bv : bv 5) P2. prreg HS (3%bv : bv 5) P3. prreg HS (4%bv : bv 5) P4.
  prreg HS (10%bv : bv 5) P10. prreg HS (11%bv : bv 5) P11.
  lazymatch goal with |- SRr _ _ (mkCfg (mkst ?rT _ ?mT _) _) _ => set (rT0 := rT) in *; set (mT0 := mT) in * end.
  assert (HKc : forall y, 0 <= y < 2 ^ 64 -> ~ (sp0 - STK_reac_declared_vlan_add <= y < sp0) -> rdW W mT0 y = rdW W mem y)
    by (intros y Hy1 Hy2; rewrite (KEEP2 y Hy1); exact (HKY1 y Hy1 Hy2)).
  assert (HspT : spZ rT0 = sp0 + -112) by (unfold spZ at 1; rewrite P2, (EE 2%nat 2%bv eq_refl), R2; unfold w64; apply unsigned_lit_small; lia).
  assert (P3' : getr rT0 3 = w64 (as_gp B)) by (rewrite P3, (EE 3%nat 3%bv eq_refl), R3; exact Hgp).
  assert (P4' : getr rT0 4 = w64 (as_tp B)) by (rewrite P4, (EE 4%nat 4%bv eq_refl), R4; exact Htp).
  assert (HraT : YK0s.ret_ok (getr rT0 1)) by (rewrite P1; apply ret_ok_codeptr_v; [unfold VAD_RCMP; lia | reflexivity]).
  assert (P10' : getr rT0 10 = w64 Q) by (rewrite P10; exact E33).
  assert (P11' : getr rT0 11 = w64 par) by (rewrite P11, (EE 19%nat 19%bv eq_refl); exact R19).
  destruct vad_par_bytes as (pb & Zpb & Hpb0 & Lpb & STRp).
  destruct (vad_par_call pb rT0 mT0 (fun y => 0 <= y < 2 ^ 64 /\ ~ (sp0 - STK_reac_declared_vlan_add <= y < sp0)) Zpb Hpb0 Lpb STRp
    ltac:(intros y [Hy1 Hy2]; exact (HKc y Hy1 Hy2)) ltac:(intros y Hy; cbv beta; lia) ltac:(intros y Hy; cbv beta; unfold SB in Hy; lia) ltac:(lia))
    as (STRb & RDb & TLb & _).
  destruct (vad_ent_call i sx rT0 mT0 _ Hi Lsx ltac:(apply (astr_atR_kept (rdW W mem1) (rdW W mT0) (sp0 - STK_reac_declared_vlan_add) sp0); [intros y Hy _; rewrite (KEEP2 y Hy); exact (KEEP1 y Hy) | exact STRx | lia | lia | lia]) (proj1 HJ) ltac:(lia)) as (STRa & RDa & TLa).
  eapply SRr_bind.
  { eapply (aj_art_at SEGS B LAWS pa_segs_low errno_low (2 * ESTACK) (fun _ => False) (SIG SS___interceptor_trampoline_strcmp)
      W rT0 mT0 STK_reac_declared_vlan_add sp0 vad_FP ly S W mem md [] ly S _ 0 (-112) (Z_to_bv 64 (BASE + VAD_RCMP)) _ HJ HspT eq_refl
      ltac:(lia) ltac:(lia) ltac:(rewrite HST, Hes; lia) P1 (fun a0 (H : False) => False_ind _ H)).
    apply (ASTRCMP fx ly S W rT0 mT0 _ Q par sx pb).
    - exact (ecall_pre_stk_at SEGS B (2 * ESTACK) STK_reac_declared_vlan_add sp0 vad_FP ly S W mem md [] ly S W mT0 _ 0 rT0 (-112)
        HJ HspT eq_refl ltac:(lia) ltac:(rewrite Hes; lia) ltac:(rewrite HST, Hes; lia) HraT P3' P4').
    - exact P10'. - exact P11'. - lia. - lia.
    - exact STRa. - exact STRb. - exact RDa. - exact RDb. - exact TLa. - exact TLb.
    - apply (vad_rom_at mT0 (fun y => 0 <= y < 2 ^ 64 /\ ~ (sp0 - STK_reac_declared_vlan_add <= y < sp0))); [intros y [Hy1 Hy2]; exact (HKc y Hy1 Hy2) | intros y Hy; cbv beta; unfold kImgEnd in Hy; lia]. }
  cbv beta. intros W2 c2 _ (-> & regs2 & mem2 & md2 & -> & HJ2 & HP2 & HQ2 & HK2).
  (* back at 0x89efc *)
  jafter_call_keep_pi HS 48%nat regs2 (mrestrict (w_H W) mem2) HP2 (@nil nat) HS2.
  match type of HS2 with ?tt -> _ => assert (HRK : tt); [|specialize (HS2 HRK); clear HRK] end.
  { apply Forall_nil. }
  clear HS. rewrite <- restrict_mkst_fx in HS2. rename HS2 into HS.
  lazymatch type of HS with st_ok_pi _ _ ?Ec _ _ =>
    assert (A52 : ew Ec 52 = getr regs2 10) by reflexivity;
    assert (OLD3 : forall k, (k < 48)%nat -> ew Ec k = ew E k)
      by (intros k Hk; cbn [ew havoc]; replace (k <? 48)%nat with true by (symmetry; apply Nat.ltb_lt; exact Hk);
          cbn [ew ewset]; repeat (rewrite (proj2 (Nat.eqb_neq _ _)) by lia); reflexivity);
    assert (HEI3 : img_env VAL A_LIM Ec) by (apply img_env_havoc; [exact HEI1 | cbv; lia]);
    assert (SHOK3 : sh_ok SEGS vad_Bx [] Ec (mrestrict (w_H W) mem2)) by apply Forall_nil end.
  assert (Usp3 : bv_unsigned (ew (havoc (ewset (ewset E 1024 w) 1025 w0) 48 (map (getr regs2) CLOB)) 2) = sp0 - 112)
    by (rewrite OLD3 by lia; exact Usp).
  assert (KEEPk : forall y, 0 <= y < 2 ^ 64 -> ~ (sp0 - 112 - 2 * ESTACK <= y < sp0 - 112) -> rdW W mem2 y = rdW W mT0 y)
    by (intros y Hy Hn; apply HK2; [exact Hy | lia | tauto]).
  clear HK2. clear HJ. rename HJ2 into HJ.
  psrr_branch_tok RUN BR HS SHOK3 Bspan.
  + (* a0 = 0: the parents agree, a duplicate: 0x89fa8 s4 = 0, the epilogue *)
    assert (HSX : sx = pb).
    { apply HQ2. pose proof (bv_unsigned_in_range 64 (getr regs2 10)) as HR10. change (bv_modulus 64) with (2 ^ 64) in HR10.
      rewrite branch_eq_U, U_SOff, U_SLit, A52, Z.add_0_r in Hc. change (zcanon 0) with 0 in Hc.
      rewrite zcanon_small in Hc by exact HR10. apply Z.eqb_eq in Hc.
      apply bv_eq. rewrite Hc. symmetry. apply unsigned_lit_small. lia. }
    assert (HM : vad_match vid p e = true).
    { unfold vad_match. fold vi. rewrite HEQ, Z.eqb_refl. cbn [andb]. apply Z.eqb_eq.
      rewrite <- Zsx, <- Zpb. apply (proj2 (SegBridge.bridge_strcmp sx pb Hsx0 Hpb0)). exact HSX. }
    assert (HD : existsb (vad_match vid p) t = true).
    { rewrite HEX, (vad_existsb_skipn_S (vad_match vid p) t i ([], 0) Hi). fold e. rewrite HM. reflexivity. }
    paj_run_to_tok RUNTO HS HJ SHOK3 Bspan VAD_EPI.
    { awr_ok_tac; exact Usp3. }
    vad_md.
    vad_keep_empty HFr KEEP3. clear HF HFr HG.
    pmkst HS.
    prreg HS (2%bv : bv 5) F2. prreg HS (3%bv : bv 5) F3. prreg HS (4%bv : bv 5) F4. prreg HS (20%bv : bv 5) F20.
    rewrite ?OLD3 in F2, F3, F4 by lia.
    apply (vad_keep 0 _ _ _ (vad_vlan_add_dup t max p vid HD)).
    * apply (vad_cut_kept regs1 mem1 md1 _ _ _ (sp0 - 112 - 2 * ESTACK) (sp0 - 112) HCUT HJ); [| lia | lia
        | rewrite F2; apply EE; reflexivity | rewrite F3; apply EE; reflexivity | rewrite F4; apply EE; reflexivity].
      intros x Hx Hn. rewrite (KEEP3 x Hx), (KEEPk x Hx Hn), (KEEP2 x Hx). exact (KEEP1 x Hx).
    * rewrite F20. reflexivity.
  + (* a0 <> 0: the parents differ; the latch *)
    assert (HSX : sx <> pb).
    { intros HS0. apply HQ2 in HS0. pose proof (bv_unsigned_in_range 64 (getr regs2 10)) as HR10. change (bv_modulus 64) with (2 ^ 64) in HR10.
      rewrite branch_eq_U, U_SOff, U_SLit, A52, Z.add_0_r in Hc. change (zcanon 0) with 0 in Hc.
      rewrite zcanon_small in Hc by exact HR10. apply Z.eqb_neq in Hc. apply Hc. rewrite HS0. apply unsigned_lit_small. lia. }
    assert (HM : vad_match vid p e = false).
    { unfold vad_match. fold vi. rewrite HEQ, Z.eqb_refl. cbn [andb]. apply Z.eqb_neq. intros Hq. apply HSX.
      apply (proj1 (SegBridge.bridge_strcmp sx pb Hsx0 Hpb0)). rewrite Zsx, Zpb. exact Hq. }
    paj_run_to_tok RUNTO HS HJ SHOK3 Bspan VAD_LT.
    { awr_ok_tac; exact Usp3. }
    vad_md.
    vad_keep_empty HFr KEEP3. clear HF HFr HG.
    pmkst HS.
    prreg HS (2%bv : bv 5) Q2. prreg HS (3%bv : bv 5) Q3. prreg HS (4%bv : bv 5) Q4.
    prreg HS (8%bv : bv 5) Q8. prreg HS (9%bv : bv 5) Q9. prreg HS (18%bv : bv 5) Q18. prreg HS (19%bv : bv 5) Q19.
    prreg HS (20%bv : bv 5) Q20. prreg HS (21%bv : bv 5) Q21. prreg HS (22%bv : bv 5) Q22. prreg HS (23%bv : bv 5) Q23.
    prreg HS (24%bv : bv 5) Q24. prreg HS (25%bv : bv 5) Q25. prreg HS (26%bv : bv 5) Q26. prreg HS (27%bv : bv 5) Q27.
    rewrite ?OLD3 in Q2, Q3, Q4, Q8, Q9, Q18, Q19, Q20, Q21, Q22, Q23, Q24, Q25, Q26, Q27 by lia.
    apply KLT. split; [|split; [|split; [exact Hi|]]].
    * apply (vad_cut_kept regs1 mem1 md1 _ _ _ (sp0 - 112 - 2 * ESTACK) (sp0 - 112) HCUT HJ); [| lia | lia
        | rewrite Q2; apply EE; reflexivity | rewrite Q3; apply EE; reflexivity | rewrite Q4; apply EE; reflexivity].
      intros x Hx Hn. rewrite (KEEP3 x Hx), (KEEPk x Hx Hn), (KEEP2 x Hx). exact (KEEP1 x Hx).
    * split; [rewrite Q8; rewrite (EE 8%nat 8%bv eq_refl); exact R8|].
      split; [rewrite Q9; rewrite (EE 9%nat 9%bv eq_refl); exact R9|].
      split; [rewrite Q18; rewrite (EE 18%nat 18%bv eq_refl); exact R18|].
      split; [rewrite Q19; rewrite (EE 19%nat 19%bv eq_refl); exact R19|].
      split; [rewrite Q20; rewrite (EE 20%nat 20%bv eq_refl); exact R20|].
      split; [rewrite Q21; rewrite (EE 21%nat 21%bv eq_refl); exact R21|].
      split; [rewrite Q24; exact E32|].
      split; [rewrite Q25; rewrite (EE 25%nat 25%bv eq_refl); exact R25|].
      rewrite Q26; rewrite (EE 26%nat 26%bv eq_refl); exact R26.
    * split.
      { rewrite HEX, (vad_existsb_skipn_S (vad_match vid p) t i ([], 0) Hi). fold e. rewrite HM. reflexivity. }
      split; [rewrite Q23, E33; reflexivity|].
      split; [rewrite Q22, E33u; reflexivity|].
      rewrite Q27, (EE 27%nat 27%bv eq_refl); exact R27.
Qed.

(* ---------- the search loop ---------- *)
Lemma vad_loop_all : forall dd i, (i + dd = length t)%nat ->
(forall r m d, vad_AFTc r m d -> SRr SEGS W (mkCfg (mkst r (Z_to_bv 64 (BASE + VAD_AFT)) m (seg_rom SEGS)) d) vad_Q) ->
forall r m d, vad_LHc i r m d -> SRr SEGS W (mkCfg (mkst r (Z_to_bv 64 (BASE + VAD_LH)) m (seg_rom SEGS)) d) vad_Q.
Proof using vad_allc.
induction dd as [|dd IH]; intros i Hd KAFT r m d HLH.
- exfalso. destruct HLH as (_ & _ & Hi & _). lia.
- apply (vad_step i r m d HLH). intros r' m' d' HLT. apply (vad_latch i r' m' d' HLT); [|exact KAFT].
  intros Hsi r'' m'' d'' HLH'. apply (IH (Datatypes.S i)); [lia | exact KAFT | exact HLH'].
Qed.

(* ---------- after the search: 0x89f28, bge; the append calls ---------- *)
Lemma vad_bge_atoms : forall E k1 k2 v1 v2, ew E k1 = w64 v1 -> ew E k2 = w64 v2 -> 0 <= v1 < 2 ^ 63 -> 0 <= v2 < 2 ^ 63 ->
branch_taken BC_GE (sv_denot E (SOff k1 0)) (sv_denot E (SOff k2 0)) = (v2 <=? v1).
Proof using.
intros E k1 k2 v1 v2 Hk1 Hk2 Hv1 Hv2. cbn [branch_taken sv_denot]. rewrite Hk1, Hk2, !Z.add_0_r. unfold w64.
rewrite !unsigned_lit_small by lia.
unfold bv_lts. rewrite !signed_lit. rewrite !zcanon_small by lia. rewrite !vad_swrap_small by lia.
destruct (Z.ltb_spec v1 v2); destruct (Z.leb_spec v2 v1); try reflexivity; lia.
Qed.
Lemma vad_add_mul18 : forall a i, 0 <= a -> 0 <= i -> a + 18 * i < 2 ^ 64 ->
alu64 ALU_ADD (Z_to_bv 64 a) (mul_div M_MUL (Z_to_bv 64 i) (Z_to_bv 64 18)) = Z_to_bv 64 (a + 18 * i).
Proof using.
intros a i H0 H1 H2. apply bv_eq. rewrite alu64_unsigned, mul_div_unsigned. cbn [zalu_raw zmd_raw].
rewrite !unsigned_lit_small by lia.
rewrite (bv_wrap_small 64 (i * 18)) by (change (bv_modulus 64) with (2 ^ 64); lia).
rewrite bv_wrap_small by (change (bv_modulus 64) with (2 ^ 64); lia). lia.
Qed.
Lemma vad_aft_seed : forall regs1 mem1,
getr regs1 2 = w64 (sp0 - 112) -> getr regs1 24 = w64 SB -> getr regs1 8 = w64 n ->
getr regs1 25 = w64 (SB + n / 8) -> getr regs1 26 = w64 L ->
sa_val (rdW W mem1) n 4 L -> range_addressable (rdW W mem1) SHADOW_OFF n 4 ->
st_ok_pi SEGS VAL (Eimg (Ereg regs1 (map w64 [SB; n; L]))) vad_ss_aft
  (restrict (w_H W) (mkst regs1 (Z_to_bv 64 (BASE + VAD_AFT)) mem1 (seg_rom SEGS)))
/\ sh_ok SEGS vad_Bx vad_aft_SH (Eimg (Ereg regs1 (map w64 [SB; n; L]))) (mrestrict (w_H W) mem1).
Proof using vad_all.
intros regs1 mem1 R2 R24 R8 R25 R26 VN RAN.
pose proof vad_sp as (Hal16 & Hslo & Hshi & _). pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof vad_tab_facts as (T1 & T2 & T3 & T4 & T5 & T6). pose proof vad_n_facts as (N1 & N2 & N3 & N4 & N5 & N6 & N7).
assert (HST : STK_reac_declared_vlan_add = 8304) by reflexivity.
set (E := Eimg (Ereg regs1 (map w64 [SB; n; L]))).
assert (EE : forall k (r : bv 5), Z.of_nat k = bv_unsigned r -> ew E k = getr regs1 r) by (intros k r Hk; apply ew_Eimg_Ereg_nat; exact Hk).
assert (Usp : bv_unsigned (ew E 2) = sp0 - 112) by (rewrite (EE 2%nat 2%bv eq_refl), R2; apply unsigned_lit_small; lia).
pose proof (vad_ex_w64 regs1 [SB; n; L] 0 ltac:(unfold A_TEXT; lia) ltac:(cbn; lia)) as E32.
pose proof (vad_ex_w64 regs1 [SB; n; L] 1 ltac:(unfold A_TEXT; lia) ltac:(cbn; lia)) as E33.
pose proof (vad_ex_w64 regs1 [SB; n; L] 2 ltac:(unfold A_TEXT; lia) ltac:(cbn; lia)) as E34.
cbn [nth Nat.add] in E32, E33, E34. fold E in E32, E33, E34.
assert (E32u : bv_unsigned (ew E 32) = SB) by (rewrite E32; apply unsigned_lit_small; unfold SB; lia).
assert (E33u : bv_unsigned (ew E 33) = n) by (rewrite E33; apply unsigned_lit_small; lia).
assert (E34u : bv_unsigned (ew E 34) = L) by (rewrite E34; apply unsigned_lit_small; lia).
assert (SHX : sv_denot E (vad_shx 33) = getr regs1 25).
{ rewrite R25. cbn [vad_shx sv_denot]. rewrite E33, E32, Z.add_0_r, Z.add_0_r. unfold w64.
  rewrite !Z_to_bv_bv_unsigned. apply vad_shx_val. lia. }
split.
- rewrite restrict_mkst_fx. unfold vad_ss_aft. apply pa_entry_st_ok_full.
  + vad_regs_ok EE ltac:(rewrite ?E32u, ?E33u, ?E34u; try (rewrite vad_shx_val by lia)).
  + vm_compute. reflexivity.
  + apply Forall_cons; [|apply Forall_nil]. unfold region_ok, vad_nregionA.
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val]. rewrite E33u.
    split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
    apply Forall_cons; [|apply Forall_nil].
    apply (chunk_ok_val SEGS E _ n 0 4 (SOff 34 0) L); [cbn [sv_denot]; rewrite E34u, Z.add_0_r; try reflexivity | cbn; lia | cbn; lia |].
    rewrite Z.add_0_r. apply vad_val_mem_of_sa. exact VN.
  + cbn. tauto.
  + split; [|split; exact I]. cbn [f_atoms atoms_ok]. unfold afact_ok, vad_spF, vad_SBF. cbn [af_lo af_hi af_al2].
    rewrite Usp, E32u, E33u, E34u. change (2 ^ 4) with 16. change (2 ^ 2) with 4. rewrite !Z.pow_0_r, !Z.mod_1_r.
    repeat split; try lia; first [rewrite Zminus_mod, Hal16; reflexivity | assumption].
- unfold sh_ok, vad_aft_SH. apply Forall_cons; [|apply Forall_nil].
  apply (vad_shent_ok E _ _ 33 n 0 4 E32 E33u); try lia.
  + rewrite Z.add_0_r. exact RAN.
  + intros y Hy. apply N5. lia.
Qed.

Lemma vad_aft : forall regs1 mem1 md1, vad_AFTc regs1 mem1 md1 ->
SRr SEGS W (mkCfg (mkst regs1 (Z_to_bv 64 (BASE + VAD_AFT)) mem1 (seg_rom SEGS)) md1) vad_Q.
Proof using vad_allm.
intros regs1 mem1 md1 (HCUT & (R8 & R9 & R18 & R19 & R20 & R21 & R24 & R25 & R26) & HEX).
pose proof HCUT as ((HJ & HFR & R2 & R3 & R4) & HK).
pose proof HPRE as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof vad_sp as (Hal16 & Hslo & Hshi & HAC4). pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof vad_tab_facts as (T1 & T2 & T3 & T4 & T5 & T6). pose proof vad_n_facts as (N1 & N2 & N3 & N4 & N5 & N6 & N7).
pose proof vad_par_facts as (Pp0 & Pp1 & Pp2).
pose proof HADD as ((_ & _ & _ & _ & (bk & mk & Hbm & Hb1 & Hb2) & HTA & HTM & _ & _ & HNV & HDST & HNA & HDJ) & Hpz & HSTR & HPA & HPL & HPM & HLOC & HPDJ & Hvid).
assert (HST : STK_reac_declared_vlan_add = 8304) by reflexivity. assert (Hes : ESTACK = 4096) by reflexivity.
unfold seg_spec.RVLAN_SIZE, sa_disj in *.
assert (HKY : forall y, 0 <= y < 2 ^ 64 -> ~ (sp0 - STK_reac_declared_vlan_add <= y < sp0) -> rdW W mem1 y = rdW W mem y)
  by (intros y Hy1 Hy2; exact (HK y Hy1 Hy2)).
assert (HKYP : forall y, (0 <= y < 2 ^ 64 /\ ~ (sp0 - STK_reac_declared_vlan_add <= y < sp0)) -> rdW W mem1 y = rdW W mem y)
  by (intros y [Hy1 Hy2]; exact (HK y Hy1 Hy2)).
assert (VN1 : sa_val (rdW W mem1) n 4 L) by (apply (vad_sa_val_keep _ _ _ _ _ _ HKYP HNV); intros k Hk; cbv beta; lia).
assert (RAN1 : range_addressable (rdW W mem1) SHADOW_OFF n 4).
{ apply (vad_ra_keep (rdW W mem) _ _ _ _ HKYP); [destruct HNA as (_ & _ & _ & HRA & _); exact HRA|].
  intros x Hx. cbv beta. rewrite <- SB_SHADOW_OFF. unfold shadow_of_addr.
  assert (0 <= x / 8 < 2 ^ 44) by (split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]). unfold SB. lia. }
destruct (vad_aft_seed regs1 mem1 R2 R24 R8 R25 R26 VN1 RAN1) as [HS SHOK].
assert (HEI : img_env VAL A_LIM (Eimg (Ereg regs1 (map w64 [SB; n; L])))) by apply Eimg_env.
assert (EE : forall k (r : bv 5), Z.of_nat k = bv_unsigned r -> ew (Eimg (Ereg regs1 (map w64 [SB; n; L]))) k = getr regs1 r)
  by (intros k r Hk; apply ew_Eimg_Ereg_nat; exact Hk).
pose proof (vad_ex_w64 regs1 [SB; n; L] 0 ltac:(unfold A_TEXT; lia) ltac:(cbn; lia)) as E32.
pose proof (vad_ex_w64 regs1 [SB; n; L] 1 ltac:(unfold A_TEXT; lia) ltac:(cbn; lia)) as E33.
pose proof (vad_ex_w64 regs1 [SB; n; L] 2 ltac:(unfold A_TEXT; lia) ltac:(cbn; lia)) as E34.
cbn [nth Nat.add] in E32, E33, E34.
remember (Eimg (Ereg regs1 (map w64 [SB; n; L]))) as E eqn:HE. clear HE.
assert (Usp : bv_unsigned (ew E 2) = sp0 - 112) by (rewrite (EE 2%nat 2%bv eq_refl), R2; apply unsigned_lit_small; lia).
assert (E33u : bv_unsigned (ew E 33) = n) by (rewrite E33; apply unsigned_lit_small; lia).
assert (E34u : bv_unsigned (ew E 34) = L) by (rewrite E34; apply unsigned_lit_small; lia).
paj_run_tok RUN HS HJ SHOK Bspan.
{ awr_ok_tac; exact Usp. }
vad_md.
vad_keep_empty HFr KEEP1. clear HF HFr HG.
assert (E21 : ew E 21 = w64 max) by (rewrite (EE 21%nat 21%bv eq_refl); exact R21).
psrr_branch_tok RUN BR HS SHOK Bspan.
- (* count >= max: full, -1 *)
  rewrite (vad_bge_atoms E 34 21 L max E34 E21) in Hc by lia. apply Z.leb_le in Hc.
  paj_run_to_tok RUNTO HS HJ SHOK Bspan VAD_EPI.
  { awr_ok_tac; exact Usp. }
  vad_md.
  vad_keep_empty HFr KEEP2. clear HF HFr HG.
  pmkst HS.
  prreg HS (2%bv : bv 5) F2. prreg HS (3%bv : bv 5) F3. prreg HS (4%bv : bv 5) F4. prreg HS (20%bv : bv 5) F20.
  apply (vad_keep (-1) _ _ _ (vad_vlan_add_full t max p vid HEX Hc)).
  + apply (vad_cut_kept regs1 mem1 md1 _ _ _ (sp0 - STK_reac_declared_vlan_add) (sp0 - STK_reac_declared_vlan_add) HCUT HJ); [| lia | lia
      | rewrite F2; apply EE; reflexivity | rewrite F3; apply EE; reflexivity | rewrite F4; apply EE; reflexivity].
    intros x Hx _. rewrite (KEEP2 x Hx). exact (KEEP1 x Hx).
  + rewrite F20, (EE 20%nat 20%bv eq_refl). exact R20.
- (* count < max: the append *)
  rewrite (vad_bge_atoms E 34 21 L max E34 E21) in Hc by lia. apply Z.leb_gt in Hc. rename Hc into LT.
  paj_run_tok RUN HS HJ SHOK Bspan.
  { awr_ok_tac; exact Usp. }
  vad_md.
  vad_keep_empty HFr KEEP2. clear HF HFr HG.
  pmkst HS.
  prreg HS (1%bv : bv 5) P1. prreg HS (2%bv : bv 5) P2. prreg HS (3%bv : bv 5) P3. prreg HS (4%bv : bv 5) P4.
  prreg HS (10%bv : bv 5) P10. prreg HS (11%bv : bv 5) P11. prreg HS (12%bv : bv 5) P12.
  set (D := tab + 18 * L) in *.
  lazymatch goal with |- SRr _ _ (mkCfg (mkst ?rT _ ?mT _) _) _ => set (rT0 := rT) in *; set (mT0 := mT) in * end.
  assert (HKc : forall y, 0 <= y < 2 ^ 64 -> ~ (sp0 - STK_reac_declared_vlan_add <= y < sp0) -> rdW W mT0 y = rdW W mem y)
    by (intros y Hy1 Hy2; rewrite (KEEP2 y Hy1), (KEEP1 y Hy1); exact (HKY y Hy1 Hy2)).
  assert (HKcP : forall y, (0 <= y < 2 ^ 64 /\ ~ (sp0 - STK_reac_declared_vlan_add <= y < sp0)) -> rdW W mT0 y = rdW W mem y)
    by (intros y [Hy1 Hy2]; exact (HKc y Hy1 Hy2)).
  assert (HspT : spZ rT0 = sp0 + -112) by (unfold spZ at 1; rewrite P2, (EE 2%nat 2%bv eq_refl), R2; unfold w64; apply unsigned_lit_small; lia).
  destruct (al_blocks _ _ LAWS ly S W mT0 _ bk mk (proj1 HJ) Hbm) as (_ & _ & _ & _ & HppresT & _).
  pose proof (req_size_pos0 mk ltac:(lia)) as [_ Hreq].
  eapply SRr_bind.
  { eapply (aj_intrin_atS SEGS B LAWS pa_segs_low OSet (SIG SS___asan_memset) (AMEMSET fx) W rT0 mT0 STK_reac_declared_vlan_add sp0 vad_FP
      ly S W mem md [] ly S _ 0 D 0 18 (-112) (Z_to_bv 64 (BASE + VAD_RMS)) HJ).
    - rewrite P10, (EE 18%nat 18%bv eq_refl), E34, R18. unfold w64. apply vad_add_mul18; lia.
    - rewrite P11. reflexivity.
    - rewrite P12. reflexivity.
    - lia.
    - lia.
    - lia.
    - exact HspT.
    - reflexivity.
    - lia.
    - rewrite HST, Hes. lia.
    - rewrite P3, (EE 3%nat 3%bv eq_refl), R3. exact Hgp.
    - rewrite P4, (EE 4%nat 4%bv eq_refl), R4. exact Htp.
    - exact P1.
    - apply ret_ok_codeptr_v; [unfold VAD_RMS; lia | reflexivity].
    - intros a Ha. split; [apply vad_awr_tab; [exact HEX | exact LT | lia] | rewrite Hes; lia].
    - intros a Ha _ _. apply (apresent_writable SEGS). exact (proj1 (HppresT a ltac:(lia))).
    - apply (vad_amem_sub tab (18 * max + 8)); [exact HTM | lia | lia | lia].
    - apply (vad_ra_keep (rdW W mem) _ _ _ _ HKcP).
      + destruct HTA as (_ & _ & _ & HRA & _). apply (range_addressable_sub _ _ tab (18 * max)); [exact HRA | lia | lia].
      + intros x Hx. cbv beta. rewrite <- SB_SHADOW_OFF. unfold shadow_of_addr.
        assert (0 <= x / 8 < 2 ^ 44) by (split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]). unfold SB. lia.
    - intros _. apply (vad_hull_keep (rdW W mem) _ _ _ _ HKcP).
      + destruct HTA as (_ & _ & _ & _ & HHV). apply (vad_hull_sub _ tab (18 * max)); [apply HHV; lia | lia | lia | lia].
      + intros s Hs. cbv beta. unfold shadow_addr in Hs. rewrite <- SB_SHADOW_OFF in Hs.
        assert (0 <= D / 8 < 2 ^ 44) by (split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]).
        assert (0 <= (D + 18 - 1) / 8 < 2 ^ 44) by (split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]).
        unfold SB in *. Z.div_mod_to_equations. lia.
    - exact I. }
  cbv beta. intros W2 c2 _ (-> & regs2 & mem2 & md2 & -> & HJ2 & HP2 & Ha02 & Heff2 & Hfr2 & Hpres2 & Hsame2).
  (* back at 0x89f44: the memset wrote [D, D + 18) and its window, nothing else *)
  assert (HK2 : forall y, 0 <= y < 2 ^ 64 -> ~ (sp0 - STK_reac_declared_vlan_add <= y < sp0) -> ~ (D <= y < D + 18) -> rdW W mem2 y = rdW W mem y).
  { intros y Hy1 Hy2 Hy3. rewrite (Hfr2 y Hy1 Hy3) by lia. exact (HKc y Hy1 Hy2). }
  assert (HK2P : forall y, (0 <= y < 2 ^ 64 /\ ~ (sp0 - STK_reac_declared_vlan_add <= y < sp0) /\ ~ (D <= y < D + 18)) -> rdW W mem2 y = rdW W mem y)
    by (intros y (Hy1 & Hy2 & Hy3); exact (HK2 y Hy1 Hy2 Hy3)).
  assert (VN2 : sa_val (rdW W mem2) n 4 L) by (apply (vad_sa_val_keep _ _ _ _ _ _ HK2P HNV); intros k Hk; cbv beta; lia).
  assert (VNT : sa_val (rdW W mT0) n 4 L) by (apply (vad_sa_val_keep _ _ _ _ _ _ HKcP HNV); intros k Hk; cbv beta; lia).
  jafter_call_keep_pi HS 48%nat regs2 (mrestrict (w_H W) mem2) HP2 [0]%nat HS2.
  match type of HS2 with ?tt -> _ => assert (HRK : tt); [|specialize (HS2 HRK); clear HRK] end.
  { apply Forall_cons; [|apply Forall_nil]. cbn [ms_mem restrict].
    apply (region_kept_val_at _ _ _ 33 n 4 L 0 0 _ E33u); [apply vad_val_mem_of_sa; exact VNT | apply vad_val_mem_of_sa; exact VN2 | lia]. }
  clear HS. rewrite <- restrict_mkst_fx in HS2. rename HS2 into HS.
  lazymatch type of HS with st_ok_pi _ _ ?Ec _ _ =>
    assert (OLD3 : forall k, (k < 48)%nat -> ew Ec k = ew E k)
      by (intros k Hk; cbn [ew havoc]; replace (k <? 48)%nat with true by (symmetry; apply Nat.ltb_lt; exact Hk); reflexivity);
    assert (HEI3 : img_env VAL A_LIM Ec) by (apply img_env_havoc; [exact HEI | cbv; lia]) end.
  assert (Usp3 : bv_unsigned (ew (havoc E 48 (map (getr regs2) CLOB)) 2) = sp0 - 112) by (rewrite OLD3 by lia; exact Usp).
  assert (RAN2 : range_addressable (rdW W mem2) SHADOW_OFF n 4).
  { apply (vad_ra_keep (rdW W mem) _ _ _ _ HK2P); [destruct HNA as (_ & _ & _ & HRA & _); exact HRA|].
    intros x Hx. cbv beta. rewrite <- SB_SHADOW_OFF. unfold shadow_of_addr.
    assert (0 <= x / 8 < 2 ^ 44) by (split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]).
    split; [unfold SB; lia|]. split; [unfold SB; lia|]. intros Hin. apply (T5 (SB + x / 8)); [lia | lia]. }
  assert (SHOK3 : sh_ok SEGS vad_Bx vad_aft_SH (havoc E 48 (map (getr regs2) CLOB)) (mrestrict (w_H W) mem2)).
  { unfold sh_ok, vad_aft_SH. apply Forall_cons; [|apply Forall_nil].
    apply (vad_shent_ok _ _ _ 33 n 0 4); [rewrite OLD3 by lia; exact E32 | rewrite OLD3 by lia; exact E33u | lia | lia | lia | rewrite Z.add_0_r; exact RAN2 | intros y Hy; apply N5; lia]. }
  clear HJ. rename HJ2 into HJ.
  paj_run_tok RUN HS HJ SHOK3 Bspan.
  { awr_ok_tac; exact Usp3. }
  vad_md.
  vad_keep_empty HFr KEEP3. clear HF HFr HG.
  pmkst HS.
  (* the strncpy call at 0x89f60: strncpy(D, parent, 15) *)
  prreg HS (1%bv : bv 5) Q1. prreg HS (2%bv : bv 5) Q2. prreg HS (3%bv : bv 5) Q3. prreg HS (4%bv : bv 5) Q4.
  prreg HS (10%bv : bv 5) Q10. prreg HS (11%bv : bv 5) Q11. prreg HS (12%bv : bv 5) Q12.
  rewrite ?OLD3 in Q2, Q3, Q4, Q10, Q11 by lia.
  lazymatch goal with |- SRr _ _ (mkCfg (mkst ?rT _ ?mT _) _) _ => set (rT1 := rT) in *; set (mT1 := mT) in * end.
  assert (HKc1 : forall y, (0 <= y < 2 ^ 64 /\ ~ (sp0 - STK_reac_declared_vlan_add <= y < sp0) /\ ~ (D <= y < D + 18)) -> rdW W mT1 y = rdW W mem y)
    by (intros y (Hy1 & Hy2 & Hy3); rewrite (KEEP3 y Hy1); exact (HK2 y Hy1 Hy2 Hy3)).
  assert (HspT1 : spZ rT1 = sp0 + -112) by (unfold spZ at 1; rewrite Q2, (EE 2%nat 2%bv eq_refl), R2; unfold w64; apply unsigned_lit_small; lia).
  destruct vad_par_bytes as (pb & Zpb & Hpb0 & Lpb & STRp).
  pose proof (Z.mod_pos_bound (par + Z.of_nat (length p)) 8 ltac:(lia)) as Hm8.
  assert (HPOUT : forall y, par <= y < par + Z.of_nat (length p) - (par + Z.of_nat (length p)) mod 8 + 8 -> ~ (D <= y < D + 18)).
  { intros y Hy Hin. unfold seg_spec.cstr_span in HPDJ.
    assert (par + Z.of_nat (length p) - (par + Z.of_nat (length p)) mod 8 + 8 = par + (Z.of_nat (length p) + 1 + (- (par + Z.of_nat (length p) + 1)) mod 8))
      by (Z.div_mod_to_equations; lia).
    lia. }
  destruct (vad_par_call pb rT1 mT1 (fun y => 0 <= y < 2 ^ 64 /\ ~ (sp0 - STK_reac_declared_vlan_add <= y < sp0) /\ ~ (D <= y < D + 18))
    Zpb Hpb0 Lpb STRp HKc1
    ltac:(intros y Hy; cbv beta; split; [lia|]; split; [lia | exact (HPOUT y Hy)])
    ltac:(intros y Hy; cbv beta; split; [unfold SB in Hy; lia|]; split; [unfold SB in Hy; lia|]; intros Hin; apply (T5 y); [lia | lia])
    ltac:(lia)) as (STRb & RDb & TLb & AMb).
  destruct (al_blocks _ _ LAWS ly S W mT1 _ bk mk (proj1 HJ) Hbm) as (_ & _ & _ & _ & HppresT1 & _).
  pose proof (blk_off_imgP B ly S W mT1 _ bk mk (proj1 HJ) Hbm) as Hoi. unfold off_img in Hoi.
  eapply SRr_bind.
  { eapply (aj_art_own_at SEGS B LAWS pa_segs_low (2 * ESTACK) (fun a => D <= a < D + 15) (SIG SS___interceptor_trampoline_strncpy)
      W rT1 mT1 STK_reac_declared_vlan_add sp0 vad_FP ly S W mem md [] ly S _ 0 (-112) (Z_to_bv 64 (BASE + VAD_RSN)) _ HJ HspT1 eq_refl
      ltac:(lia) ltac:(lia) ltac:(rewrite HST, Hes; lia) Q1).
    - intros a Ha. apply vad_awr_tab; [exact HEX | exact LT | lia].
    - apply (ASTRNCPY fx ly S W rT1 mT1 _ D par 15 pb).
      + exact (ecall_pre_stk_at SEGS B (2 * ESTACK) STK_reac_declared_vlan_add sp0 vad_FP ly S W mem md [] ly S W mT1 _ 0 rT1 (-112)
          HJ HspT1 eq_refl ltac:(lia) ltac:(rewrite Hes; lia) ltac:(rewrite HST, Hes; lia)
          ltac:(rewrite Q1; apply ret_ok_codeptr_v; [unfold VAD_RSN; lia | reflexivity])
          ltac:(rewrite Q3, (EE 3%nat 3%bv eq_refl), R3; exact Hgp) ltac:(rewrite Q4, (EE 4%nat 4%bv eq_refl), R4; exact Htp)).
      + rewrite Q10, (EE 18%nat 18%bv eq_refl), E34, R18. unfold w64. apply vad_add_mul18; lia.
      + rewrite Q11, (EE 19%nat 19%bv eq_refl). exact R19.
      + rewrite Q12. reflexivity.
      + lia.
      + lia.
      + lia.
      + exact STRb.
      + apply (vad_aread_sub _ _ _ _ (astr_len pb + 1) _ RDb). unfold astr_len. lia.
      + exact AMb.
      + apply (awrite_ok_of_block SEGS B LAWS (2 * ESTACK) ly S W mT1 _ rT1 bk mk D 15 (proj1 HJ) Hbm); lia.
      + apply (vad_amem_sub tab (18 * max + 8)); [exact HTM | lia | lia | lia].
      + intros a Ha _ Hrom. destruct Hrom as (sg & Hsg & _ & Hr). assert (Himg : in_img SEGS a) by (exists sg; split; [exact Hsg | exact Hr]).
        pose proof (pa_img_range _ Himg) as HR. unfold kImgEnd in HR. lia.
      + exact TLb.
      + unfold RtString.aword_end, astr_len. unfold seg_spec.cstr_span in HPDJ. rewrite Lpb.
        destruct HPDJ as [HPD | HPD]; [right | left; lia].
        assert (Hmin : Z.min 15 (Z.of_nat (length p) + 1) <= Z.of_nat (length p) + 1) by lia.
        assert (par + Z.min 15 (Z.of_nat (length p) + 1) + (- (par + Z.min 15 (Z.of_nat (length p) + 1))) mod 8 <=
                par + (Z.of_nat (length p) + 1 + (- (par + Z.of_nat (length p) + 1)) mod 8)) by (Z.div_mod_to_equations; lia).
        lia.
      + apply (vad_rom_at mT1 _ HKc1). intros y Hy. cbv beta. unfold kImgEnd in Hy.
        split; [lia|]. split; [lia|]. intros Hin. lia. }
  cbv beta. intros W3 c3 _ (-> & regs3 & mem3 & md3 & -> & HJ3 & HP3 & (Ha03 & HB15) & Hfr3).
  (* back at 0x89f64: strncpy wrote [D, D + 15) and its window, nothing else *)
  assert (HK3 : forall y, (0 <= y < 2 ^ 64 /\ ~ (sp0 - STK_reac_declared_vlan_add <= y < sp0) /\ ~ (D <= y < D + 18)) -> rdW W mem3 y = rdW W mem y).
  { intros y (Hy1 & Hy2 & Hy3). rewrite (Hfr3 y Hy1) by lia. exact (HKc1 y (conj Hy1 (conj Hy2 Hy3))). }
  assert (VN3 : sa_val (rdW W mem3) n 4 L) by (apply (vad_sa_val_keep _ _ _ _ _ _ HK3 HNV); intros k Hk; cbv beta; lia).
  assert (VNT1 : sa_val (rdW W mT1) n 4 L) by (apply (vad_sa_val_keep _ _ _ _ _ _ HKc1 HNV); intros k Hk; cbv beta; lia).
  jafter_call_keep_pi HS 64%nat regs3 (mrestrict (w_H W) mem3) HP3 [0]%nat HS2.
  match type of HS2 with ?tt -> _ => assert (HRK : tt); [|specialize (HS2 HRK); clear HRK] end.
  { apply Forall_cons; [|apply Forall_nil]. cbn [ms_mem restrict].
    apply (region_kept_val_at _ _ _ 33 n 4 L 0 0 _); [cbn [ew ewset havoc Nat.eqb Nat.ltb]; exact E33u | apply vad_val_mem_of_sa; exact VNT1 | apply vad_val_mem_of_sa; exact VN3 | lia]. }
  clear HS. rewrite <- restrict_mkst_fx in HS2. rename HS2 into HS.
  lazymatch type of HS with st_ok_pi _ _ ?Ec _ _ =>
    assert (OLD4 : forall k, (k < 48)%nat -> ew Ec k = ew E k)
      by (intros k Hk; cbn [ew havoc ewset]; replace (k <? 64)%nat with true by (symmetry; apply Nat.ltb_lt; lia);
          repeat (rewrite (proj2 (Nat.eqb_neq _ _)) by lia); cbn [ew havoc]; replace (k <? 48)%nat with true by (symmetry; apply Nat.ltb_lt; exact Hk); reflexivity);
    assert (HEI4 : img_env VAL A_LIM Ec) by (apply img_env_havoc; [assumption | cbv; lia]) end.
  assert (RAN3 : range_addressable (rdW W mem3) SHADOW_OFF n 4).
  { apply (vad_ra_keep (rdW W mem) _ _ _ _ HK3); [destruct HNA as (_ & _ & _ & HRA & _); exact HRA|].
    intros x Hx. cbv beta. rewrite <- SB_SHADOW_OFF. unfold shadow_of_addr.
    assert (0 <= x / 8 < 2 ^ 44) by (split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]).
    split; [unfold SB; lia|]. split; [unfold SB; lia|]. intros Hin. apply (T5 (SB + x / 8)); [lia | lia]. }
  lazymatch type of HS with st_ok_pi _ _ ?Ec _ _ =>
    assert (Usp4 : bv_unsigned (ew Ec 2) = sp0 - 112) by (rewrite OLD4 by lia; exact Usp);
    assert (SHOK4 : sh_ok SEGS vad_Bx vad_aft_SH Ec (mrestrict (w_H W) mem3))
      by (unfold sh_ok, vad_aft_SH; apply Forall_cons; [|apply Forall_nil];
          apply (vad_shent_ok _ _ _ 33 n 0 4); [rewrite OLD4 by lia; exact E32 | rewrite OLD4 by lia; exact E33u | lia | lia | lia | rewrite Z.add_0_r; exact RAN3 | intros y Hy; apply N5; lia]) end.
  clear HJ. rename HJ3 into HJ.
  paj_run_to_tok RUNTO HS HJ SHOK4 Bspan VAD_ST.
  { awr_ok_tac; exact Usp4. }
  vad_md.
  vad_keep_empty HFr KEEP4. clear HF HFr HG.
  pmkst HS.
  prreg HS (2%bv : bv 5) F2. prreg HS (3%bv : bv 5) F3. prreg HS (4%bv : bv 5) F4.
  prreg HS (8%bv : bv 5) F8. prreg HS (9%bv : bv 5) F9. prreg HS (24%bv : bv 5) F24. prreg HS (10%bv : bv 5) F10.
  change (Z.to_nat 15) with 15%nat in HB15.
  assert (HSTRn : ~ In 0 p) by (destruct HSTR as ((_ & Hn) & _); exact Hn).
  assert (KFR : forall x, (0 <= x < 2 ^ 64 /\ sp0 - 112 <= x) -> rdW W (ms_mem ms2) x = rdW W mem1 x).
  { intros x (Hx1 & Hx2). rewrite (KEEP4 x Hx1), (Hfr3 x Hx1) by lia. rewrite (KEEP3 x Hx1), (Hfr2 x Hx1) by lia.
    rewrite (KEEP2 x Hx1). exact (KEEP1 x Hx1). }
  apply vad_store. fold D. split; [|split; [exact LT|]; split; [exact HEX|]].
  + split; [exact HJ|]. split.
    * intros j r Hr. assert (Hj : (j < 13)%nat) by (change 13%nat with (length vad_saved); apply (proj1 (nth_error_Some vad_saved j)); rewrite Hr; discriminate).
      apply (vad_sa_val_keep (rdW W mem1) _ _ _ _ _ KFR (HFR j r Hr)). intros k Hk. cbv beta. lia.
    * split; [rewrite F2, (EE 2%nat 2%bv eq_refl); exact R2|].
      split; [rewrite F3, (EE 3%nat 3%bv eq_refl); exact R3 | rewrite F4, (EE 4%nat 4%bv eq_refl); exact R4].
  + split; [rewrite F8; exact E33|].
    split; [rewrite F9, (EE 9%nat 9%bv eq_refl); exact R9|].
    split; [rewrite F24; exact E32|].
    split.
    { rewrite F10, (EE 18%nat 18%bv eq_refl), E34, R18. unfold w64. rewrite unsigned_lit_small by lia.
      rewrite vad_add_mul18 by lia. f_equal. lia. }
    split.
    { intros x Hx1 Hx2 Hx3. rewrite (KEEP4 x Hx1), (Hfr3 x Hx1) by lia. rewrite (KEEP3 x Hx1). exact (HK2 x Hx1 Hx2 Hx3). }
    exists ((firstn 15 pb ++ repeat (Z_to_bv 8 0) (15 - length pb)) ++ [Z_to_bv 8 0]). split.
    { rewrite !length_app, length_firstn, repeat_length. cbn [length]. lia. }
    split.
    { apply vad_sa_bytes_app. split.
      -- intros k Hk. pose proof Hk as Hk'. rewrite length_app, length_firstn, repeat_length in Hk'.
         rewrite (KEEP4 (tab + 18 * L + Z.of_nat k) ltac:(lia)). exact (HB15 k Hk).
      -- intros k Hk. cbn [length] in Hk. assert (k = 0%nat) by lia. subst k.
        rewrite length_app, length_firstn, repeat_length.
        replace (tab + 18 * L + Z.of_nat (Nat.min 15 (length pb) + (15 - length pb)) + Z.of_nat 0) with (D + 15) by lia.
        rewrite (KEEP4 (D + 15) ltac:(lia)), (Hfr3 (D + 15) ltac:(lia)) by lia. rewrite (KEEP3 (D + 15) ltac:(lia)).
        rewrite (Heff2 15 ltac:(lia)). reflexivity. }
    rewrite <- app_assoc. apply vad_new_entry_enc15; [exact Zpb | exact HSTRn | exact Hvid].
Qed.

(* ---------- the whole call: the entry stretch, the search loop, the exits ---------- *)
Lemma vad_main : SRr SEGS W (cfg_at SEGS (BASE + AF_reac_declared_vlan_add) regs mem md) vad_Q.
Proof using vad_allc vad_allm.
apply vad_entry.
- intros r m d HLH. exact (vad_loop_all (length t) 0%nat ltac:(lia) vad_aft r m d HLH).
- exact vad_aft.
Qed.

End w.

Theorem reac_declared_vlan_add_walk :
reac_declared_vlan_add_contract SEGS B (BASE + AF_reac_declared_vlan_add) STK_reac_declared_vlan_add RLO_A RHI_A.
Proof using TL ASTRCMP ASTRNCPY AMEMSET.
intros ly S W regs mem md ch tab max n parent vid t p HPRE HROD H10 _ H11 _ H12 _ H13 _ H14 _ HADD _.
exact (vad_main ly S W regs mem md ch RLO_A RHI_A tab max n parent vid t p HPRE HROD H10 H11 H12 H13 H14 HADD).
Qed.
End e.
End d.
End b.
