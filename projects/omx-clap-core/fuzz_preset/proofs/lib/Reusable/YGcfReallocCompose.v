(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by a Theorem Labs lane (ReallocPrimary.TkSecLink), 2026-10-30: the trace premise in the P'' form, `admits (as_universe B) tr S` (YG01.v), replacing the In-form. *)
(* Modified by a Theorem Labs lane (ReallocPrimary.TkSecLink), 2026-10-30: batch_room_cf added to rpreD_free_cf (YGcfMallocCompose.v) and supplied here at RDF2, the old-block free's premise, from ARX_br; the acall_prefix_cf comment updated (the conjunct is on this base since d48cd401d143). *)
(* Modified by Theorem Labs, 2026-10-30: taken by path from proofs/cgif/cgif_file_fuzzer/lib/YGcfReallocCompose.v at commit fec7cbb6287c (the cf layer of record, field rounds 1 + 2), module paths changed; the preset-side hunks kept on top are listed in the round6f report. *)
(* Modified by Theorem Labs, 2026-10-30: taken by path from proofs/cgif/cgif_file_fuzzer/lib/YGcfReallocCompose.v at commit d0377850faab (the cf layer of record, field round 3 + the hull round + pf_ial_apart_t), module paths changed; the preset-side hunks kept on top are listed in the round6g report. *)
(* Modified by Theorem Labs, 2026-10-30: field round 3 part 3 (MP) from proofs/cgif/cgif_file_fuzzer/lib/YGcfReallocCompose.v applied by 3-way (base commit 5034424e29db, theirs e8a7dd66acf2; preset-side hunks kept), module paths changed. *)
(* Theorem Labs, 2026-10: fuzz_preset's event-free allocator instance (suffix cf), row A4 of the internal file FREE-PIECES-102.md: the
   IMAGE-FREE realloc bridge, both bridges proved. From a Theorem Labs lane's frame-generic Allocate / Deallocate contracts (AllocG.v,
   DeallocG.v, with the errno twins of ErrnoGcf.v as YGcfMallocComposeE.v takes them), the realloc interceptor's walk as
   a Record, and a Theorem Labs lane's realloc composition (RGtop.v, c5: rg_realloc_all :378, rg_realloc_null :513; its model
   obligations at the instance are YGcfRmodel.rmodel_ok_cf_wf, cited, not re-derived) to the API leaves
   YGcfRealloc.arealloc_realizes_cf / arealloc_null_realizes_cf (YGcfRealloc.v:93-112); the null leaf is the body
   of pa_realloc_null_cf / pa_realloc_null_cf_B (A/CfApiPreset.v:94-96, AU/CfApiPresetB.v:107-109).
   The record's segments are RGtop's (S1 seg_pre :244, S2a seg_mid_a :261, S2b seg_mid_b :282, S3 seg_ret :302,
   S4 seg_nret :318; S5 seg_npre :340, S6 seg_npost :356) at the cf instance, with the copy routine's contract
   (ReallocG.amemcpy_realizes at cf_pc_memcpy) as a field. They differ from RGtop's text in four ways, each one forced
   by the target leaf or its premises:
   (a) the entry facts are arealloc_realizes_allP's / arealloc_null_realizesP's premises at the instance (rentry_cf /
       rnentry_cf): RGtop's rentry needs realloc_pre (ARX at the entry, ly_bot ly + RSTACK < sp) and fpre, which
       the API leaf does not give;
   (b) every segment also keeps errno's four bytes (errno_kept_cf; not on the ENOMEM arms): realloc_leaf_cf /
       malloc_leaf_cf state it, RGtop's rkeep excludes errno (it is in ascratch). Part 3c: the leaves no longer
       state the overlay normal form (memnorm), so no segment keeps it;
   (c) Deallocate's pre: the API leaf takes ~ In (sptr_addr B ly p) Hp (YGcfRealloc.v:93-104, as afree_realizes_cf,
       YG0dcf.v:192), so the old base is not hidden and Deallocate's contract is the free bridge's at Hp. S2b reaches
       Deallocate's pre at ARX Hp with fpre := True (realloc_dpre_cf: the walk proves nothing about Hp), and the bridge
       adds fpre_hp_cf from the entry; S3 carries Deallocate's post ARX at any ghost set Hp' to the return;
   (d) the owned sets are the malloc / free bridges': Allocate's post at AOXm_cf (aowned or the errbuf extent),
       Deallocate's at aowned, the interceptor's own frames (ikeep_cf, rkeep) outside aowned and the stack window.
   The invariants K1 (at Allocate's call), K2 (at the copy routine's call), K3 (at Deallocate's call) and Kn (at the
   NULL-input call of Allocate) are RGtop's, with the caller's ghost set Hp as a third argument; they are parameters
   of the records, chosen by the walk that discharges them (lanes A5 / A6).
   ARX is ARXh_t, the Hp-indexed relation of YGcfMallocCompose.v (the consumer's: YGcfDIface.ARXs_cf B segs).
   The call-site arguments (al, atp, acf of Allocate; atpD of Deallocate) and Allocate's size bound nmax are section
   variables, as in YGcfMallocCompose.v; realloc's Allocate calls pass malloc's arguments.
   STACK ROOM: AllocG.alloc_pre / DeallocG.dealloc_pre need ly_bot ly < sp at the inner calls (AllocG.v:75,
   DeallocG.v:83), below the interceptor's entry sp. acall_pre_cf bounds the entry sp by ly_bot ly + ACALL_PREFIX <
   spZ regs (a Theorem Labs lane's ACALL_PREFIX := 4096; YG0dcf.v:61, on this base since d48cd401d143), so the segments that
   reach Allocate's / Deallocate's entry (S1, S2b, S5) take ly_bot ly + 4096 < spZ regs from acall_pre_cf through
   acall_prefix_cf (section 2), the projection of that conjunct.
   a Theorem Labs lane's inputs are NAMED premises: the memnorm-kept contracts aalloc_realizes_cf_em_m / adealloc_realizes_raw_cf_em_m
   (YGcfMallocComposeE.v: MemnormT's at the cf instance; errno and memnorm from one post) and nmax_cf_ok
   (YGcfMallocCompose.v:92; nmax_cf_ok_of_w in YGcfMallocComposeE.v).
   Beyond the malloc / free bridges' premises, the bridges take named premises for the top's two pending conjuncts
   (acall_prefix_cf: the stack room; acall_xs_cf: the errbuf placement), two more projections of the consumer's ARX
   (ARX_qm, ARX_br: qmeter_cf and batch_room_cf, both ARXs_cf conjuncts) and the image fact errno_word_cf.
   The model facts are proved here: the inner malloc keeps the internal-init flag and adds only the returned
   block's chunk (ci_malloc_cf, a cfx_ipost walk as YGcfXs.v's for free_cf), and the owned set of the state between
   Allocate and Deallocate lies in the first or the last state's (aowned_mid_cf), so realloc_leaf_cf's single frame
   follows from the two calls' frames.
   No image constant; no function is proved here (rule 24). *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Bool Lia.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s YK0j YP09.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YI04.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK04 YA0i YA0n YA0o YA0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG00 YG0a YG01 YG04 YG0f YG0v YG0n YG0d.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YM05 YGcfNames YG01cf YG00cf YG0ncf YG0dcf.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YGcfTok YG06bcf YG07cf YGcfRoomPre YG03cf YG03dcf YGcfApath YG0lawscf.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require
AllocG DeallocG ReallocG ReallocP RGtop YGcfRmodel YAkMemnorm ErrnoGcf YGcfRealloc YG0s YGcfXs YGcfSecsStep.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YGcfMallocCompose YGcfMallocComposeE.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YGcfRodata.
(* stdpp, through the LPS modules, shadows several list names; In and remove here are Stdlib's, as in YGcfRealloc.v. *)
From Stdlib Require Import List.
Import ListNotations.
Local Unset Lia Cache. Local Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Open Scope Z_scope.

(* ---------------------------------------------------------------------------- *)
(* The inner malloc's path keeps the internal-init flag and adds no chunk but the  *)
(* returned block's: every IRet of malloc_cf (YG00cf.v:234) satisfies it. The        *)
(* callees touch neither field; the proof is YGcfXs.v's cfx_ipost walk (its fr_*    *)
(* tactics, :436-465, restated: Ltac does not leave its section) over this pair.     *)
Definition ci_same (s s' : astate) : Prop := st_chunks s' = st_chunks s /\ st_internal_inited s' = st_internal_inited s.

Create HintDb cidb.

Ltac ci_unf :=
progress (unfold YG00.get_region, YG00.set_region, YG00.get_pc, YG00.set_pc, YG00.init_cache_if_needed, YG00.tick,
YG00.bind, YG00.get, YG00.put, YG00.modify, YG00.askz, YG00.ret, YG00.mcheck, YG00.fail, YG00.spin, ci_same in *).

Ltac ci_cbn :=
cbn [ibind YGcfXs.cfx_ipost fst snd st_secs st_chunks st_regions st_cache st_cache_inited st_sec_arr st_sec_reserved
st_qthread st_qglobal st_fs st_depot st_internal_inited st_nev set_regions set_cache set_chunks set_secs set_sec_arr
set_sec_reserved set_depot set_cache_inited set_nev set_qglobal set_qthread set_internal_inited] in *.

Ltac ci_hint :=
first
[ match goal with |- YGcfXs.cfx_ipost (ibind _ _) _ =>
  apply YGcfXs.cfx_ipost_ibind; eapply YGcfXs.cfx_ipost_mono; [|solve [eauto with cidb]];
  let x := fresh "x" in let sx := fresh "sx" in let H1 := fresh "Hs" in let H2 := fresh "Hc" in
  intros [x sx] [H1 H2]; cbn [fst snd] in H1, H2 end
| match goal with |- YGcfXs.cfx_ipost _ _ =>
  eapply YGcfXs.cfx_ipost_mono; [|solve [eauto with cidb]];
  let x := fresh "x" in let sx := fresh "sx" in let H1 := fresh "Hs" in let H2 := fresh "Hc" in
  intros [x sx] [H1 H2]; cbn [fst snd] in H1, H2 end ].

Ltac ci_step :=
first
[ progress ci_cbn
| ci_unf
| progress intros
| match goal with |- YGcfXs.cfx_ipost (ibind (ibind _ _) _) _ => apply YGcfXs.cfx_ipost_ibind_assoc end
| ci_hint
| match goal with |- context [match ?x with _ => _ end] => destruct x end
| exact I
| split; congruence ].

Section G. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {ci : CfImg} {cp : CfParams}.

Lemma ci_ensure : forall c need sof s, YGcfXs.cfx_ipost (ensure_free_array c need sof s) (fun r => ci_same s (snd r)).
Proof. intros c need sof s. unfold ensure_free_array. repeat ci_step. Qed.
#[local] Hint Resolve ci_ensure : cidb.
Lemma ci_mmu : forall c need s, YGcfXs.cfx_ipost (map_more_user c need s) (fun r => ci_same s (snd r)).
Proof. intros c need s. unfold map_more_user. repeat ci_step. Qed.
#[local] Hint Resolve ci_mmu : cidb.
Lemma ci_populate : forall c need s, YGcfXs.cfx_ipost (populate c need s) (fun r => ci_same s (snd r)).
Proof. intros c need s. unfold populate. repeat ci_step. Qed.
#[local] Hint Resolve ci_populate : cidb.
Lemma ci_set_exh : forall c s, YGcfXs.cfx_ipost (set_exh_cf c s) (fun r => ci_same s (snd r)).
Proof. intros c s. unfold set_exh_cf. repeat ci_step. Qed.
#[local] Hint Resolve ci_set_exh : cidb.
Lemma ci_clear_exh : forall c s, YGcfXs.cfx_ipost (clear_exh_cf c s) (fun r => ci_same s (snd r)).
Proof. intros c s. unfold clear_exh_cf. repeat ci_step. Qed.
#[local] Hint Resolve ci_clear_exh : cidb.
Lemma ci_errb_set_size : forall ns s, YGcfXs.cfx_ipost (errb_set_size ns s) (fun r => ci_same s (snd r)).
Proof. intros ns s. unfold errb_set_size. repeat ci_step. Qed.
#[local] Hint Resolve ci_errb_set_size : cidb.
Lemma ci_errb_retire : forall s, YGcfXs.cfx_ipost (errb_retire s) (fun r => ci_same s (snd r)).
Proof. intros s. unfold errb_retire. repeat ci_step. Qed.
#[local] Hint Resolve ci_errb_retire : cidb.
Lemma ci_errb_map : forall w s, YGcfXs.cfx_ipost (errb_map_cf w s) (fun r => ci_same s (snd r)).
Proof. intros w s. unfold errb_map_cf. repeat ci_step. Qed.
#[local] Hint Resolve ci_errb_map : cidb.
Lemma ci_errb_append : forall len s, YGcfXs.cfx_ipost (errb_append_cf len s) (fun r => ci_same s (snd r)).
Proof. intros len s. unfold errb_append_cf. repeat ci_step. Qed.
#[local] Hint Resolve ci_errb_append : cidb.
Lemma ci_errb_report : forall c s, YGcfXs.cfx_ipost (errb_report_cf c s) (fun r => ci_same s (snd r)).
Proof. intros c s. unfold errb_report_cf. repeat ci_step. Qed.
#[local] Hint Resolve ci_errb_report : cidb.
Lemma ci_mmu_cf : forall c need s, YGcfXs.cfx_ipost (map_more_user_cf c need s) (fun r => ci_same s (snd r)).
Proof. intros c need s. unfold map_more_user_cf. repeat ci_step. Qed.
#[local] Hint Resolve ci_mmu_cf : cidb.
Lemma ci_populate_cf : forall c need s, YGcfXs.cfx_ipost (populate_cf c need s) (fun r => ci_same s (snd r)).
Proof. intros c need s. unfold populate_cf. repeat ci_step. Qed.
#[local] Hint Resolve ci_populate_cf : cidb.
Lemma ci_gfa_cf : forall c n s, YGcfXs.cfx_ipost (get_from_allocator_cf c n s) (fun r => ci_same s (snd r)).
Proof. intros c n s. unfold get_from_allocator_cf. repeat ci_step. Qed.
#[local] Hint Resolve ci_gfa_cf : cidb.
Lemma ci_refill_cf : forall c s, YGcfXs.cfx_ipost (refill_if_empty_cf c s) (fun r => ci_same s (snd r)).
Proof. intros c s. unfold refill_if_empty_cf. repeat ci_step. Qed.
#[local] Hint Resolve ci_refill_cf : cidb.
Lemma ci_cache_alloc_cf : forall c s, YGcfXs.cfx_ipost (cache_alloc_cf c s) (fun r => ci_same s (snd r)).
Proof. intros c s. unfold cache_alloc_cf. repeat ci_step. Qed.
#[local] Hint Resolve ci_cache_alloc_cf : cidb.
Lemma ci_depot : forall tr s, YGcfXs.cfx_ipost (depot_put tr s) (fun r => ci_same s (snd r)).
Proof. intros tr s. unfold depot_put. repeat ci_step. Qed.
#[local] Hint Resolve ci_depot : cidb.
Lemma ci_sec_alloc : forall n s, YGcfXs.cfx_ipost (sec_alloc n s) (fun r => ci_same s (snd r)).
Proof. intros n s. unfold sec_alloc. repeat ci_step. Qed.
#[local] Hint Resolve ci_sec_alloc : cidb.

Lemma ci_malloc_cf : forall n tr s, YGcfXs.cfx_ipost (malloc_cf n tr s) (fun r =>
st_internal_inited (snd r) = st_internal_inited s /\
(forall k, In k (st_chunks (snd r)) -> In k (st_chunks s) \/ (ck_user k = fst r /\ ck_req k = n))).
Proof.
intros n tr s. unfold malloc_cf. repeat ci_step.
all: split; [congruence|]; intros k0 Hk0.
all: first [left; congruence
  | destruct (YGcfXs.cfx_upd_in _ _ _ Hk0) as [Ek | Hk1]; [right; subst k0; split; reflexivity | left; congruence]].
Qed.

(* ---------------------------------------------------------------------------- *)
(* 0b. The model's paths the hull admission is read along (the hull field round: the caller's admission
   cf_hull_ok at the realloc's post; the composition carries it back to the state after the inner malloc).      *)

(* A tree that atok_cf proves at the flag true returns on some path: answer each request with a granting reply
   (progz q z = true keeps the flag, and a spin needs the flag false). *)
Lemma atok_cf_path_ex {A : Type} (t : itree astate A) : forall Q, atok_cf true t Q ->
exists trc a, apath t trc a /\ Q true a.
Proof.
induction t as [a | q snap k IH | pc | f]; cbn [atok_cf]; intros Q H.
- exists [], a. split; [reflexivity | exact H].
- destruct H as [_ Hk].
  assert (Z0 : exists z, aok snap q z /\ progz q z = true).
  { destruct q; cbn [aok progz];
    first [ exists 1; split; [right; reflexivity | reflexivity]
          | exists 0; split; [left; reflexivity | reflexivity]
          | exists 1; split; [reflexivity | reflexivity] ]. }
  destruct Z0 as (z & Hz & Pz).
  pose proof (Hk z Hz) as Hkz. rewrite Pz in Hkz.
  destruct (IH z Q Hkz) as (trc & a & Hp & HQ).
  exists ((q, z) :: trc), a. split; [|exact HQ].
  cbn [apath]. split; [reflexivity|]. split; [exact Hz | exact Hp].
- discriminate H.
- destruct H.
Qed.

(* The inner free of realloc(p, n) returns on some model path at the state after the inner malloc, from free's model
   contract (YG03dcf.ml_free_cf) there. *)
Lemma inner_free_path_cf : forall U s p n tr, universe_ok U -> Wf_cf U s -> batch_room_cf s ->
In (p, n) (blocks s) -> admits U tr s -> exists trc s', apath (free_cf p tr s) trc (tt, s').
Proof.
intros U s p n tr HU W BR Hb Ht.
destruct (atok_cf_path_ex _ _ (ml_free_cf U HU s p n tr W BR (or_intror Hb) Ht)) as (trc & [[] s'] & Hp & _).
exists trc, s'. exact Hp.
Qed.

(* The realloc tree's path through a block q, from its three steps' paths. *)
Lemma realloc_tree_path_cf : forall p n tr S trc1 S1 trc2 (q : sptr) S2 trc3 S3, q <> PNull ->
apath (free_cf PNull tr S) trc1 (tt, S1) -> apath (malloc_cf n tr S1) trc2 (q, S2) ->
apath (free_cf p tr S2) trc3 (tt, S3) ->
apath (ReallocP.realloc_tree_with malloc_cf free_cf p n tr S) (trc1 ++ trc2 ++ trc3 ++ []) (q, S3).
Proof.
intros p n tr S trc1 S1 trc2 q S2 trc3 S3 HQ Hp1 Hp2 Hp3.
unfold ReallocP.realloc_tree_with.
apply (RGtop.rg_apath_bind _ _ S trc1 tt S1 _ _ Hp1).
apply (RGtop.rg_apath_bind _ _ S1 trc2 q S2 _ _ Hp2).
destruct q as [| | |]; [exfalso; exact (HQ eq_refl)| | |];
  (eapply (RGtop.rg_apath_bind _ _ S2 trc3 tt S3 []); [exact Hp3 | cbn; reflexivity]).
Qed.

Section J.
Variable segs : list Segment.
Variable B : asyms.

(* acall_pre_cf's last conjunct (field round 3; part 3c: memnorm is no longer there): the read-only bytes at the
   call's memory. *)
Lemma acall_pre_cf_ro : forall ly S Hp W regs mem md ch, acall_pre_cf segs B ly S Hp W regs mem md ch ->
arodata_ok_cf segs B mem.
Proof. intros ly S Hp W regs mem md ch H. unfold acall_pre_cf in H. decompose [and] H. assumption. Qed.

Section R.
(* Allocate's size bound and its call-site arguments (YGcfMallocCompose.v Section M); Deallocate's alloc_type argument
   (Section F). *)
Variables (nmax al atp acf atpD : Z).

(* ---------------------------------------------------------------------------- *)
(* 0. The entry facts, the call-site premises, the invariants' types.            *)

(* The realloc trace: trace[0] is the interceptor's cf_pc_realloc_ra0 (YGcfRealloc.v:83-91). *)
Definition rtr_cf (ly : alayout) (regs : bvmap 5 word) (ch : list (Z * Z * Z)) : list Z :=
call_trace ly cf_pc_realloc_ra0 regs ch.

(* realloc(p, n)'s entry: arealloc_realizes_cf's premises (YGcfRealloc.v:93-101: arealloc_realizes_allP's,
   ReallocP.v:74-78, at the instance cpre := acall_pre_cf at Hp, rpre := True, nmax := cf_malloc_max, lmax := LIVE_MAX,
   U := admits (as_universe B) (the P'' trace premise, YG01.v:158), with the freed base not hidden after a0). *)
Definition rentry_cf (ly : alayout) (S : astate) (Hp : list Z) (W : world segs) (regs : bvmap 5 word)
(mem : word -> option byte) (md : Model) (p : sptr) (n_old n : Z) (ch : list (Z * Z * Z)) : Prop :=
acall_pre_cf segs B ly S Hp W regs mem md ch /\
In (p, n_old) (blocks S) /\ getr regs 10 = w64 (sptr_addr B ly p) /\ ~ In (sptr_addr B ly p) Hp /\
getr regs 11 = w64 n /\
1 <= n < cf_malloc_max /\ blocks_bytes S + n <= LIVE_MAX /\
admits (as_universe B) (rtr_cf ly regs ch) S.

(* realloc(NULL, n)'s entry: arealloc_null_realizesP's premises (ReallocP.v:85-89) at the same instance. *)
Definition rnentry_cf (ly : alayout) (S : astate) (Hp : list Z) (W : world segs) (regs : bvmap 5 word)
(mem : word -> option byte) (md : Model) (n : Z) (ch : list (Z * Z * Z)) : Prop :=
acall_pre_cf segs B ly S Hp W regs mem md ch /\
getr regs 10 = w64 0 /\ getr regs 11 = w64 n /\
1 <= n < cf_malloc_max /\ blocks_bytes S + n <= LIVE_MAX /\
admits (as_universe B) (rtr_cf ly regs ch) S.

(* Deallocate's pre at Reallocate's call, at the ghost set Hp: DeallocG.dealloc_pre at the instance of free_dpre_cf
   (YGcfMallocCompose.v:298) with fpre := True: the walk proves nothing about Hp; the bridge adds fpre_hp_cf (the old
   base not hidden, at Deallocate's layout) from the entry's premise. *)
Definition realloc_dpre_cf (ARX : ARXh_t segs) (Hp : list Z) (inst so bp : Z) (ly : alayout) (S : astate)
(W : world segs) (regs : bvmap 5 word) (mem : word -> option byte) (md : Model) (p : sptr) (n : Z) (tr : list Z) : Prop :=
DeallocG.dealloc_pre segs B (admits (as_universe B)) (ARX Hp) (rpreD_free_cf B)
(fun _ _ _ _ _ _ => True) atpD inst so bp ly S W regs mem md p n tr.

(* The invariants' types: RGtop's K1_t / K2_t / Kn_t (RGtop.v:231-239) with the caller's ghost set Hp after S. *)
Definition K1r_t : Type :=
alayout -> astate -> list Z -> world segs -> bvmap 5 word -> (word -> option byte) -> Model ->
sptr -> Z -> Z -> list (Z * Z * Z) ->
astate -> world segs -> bvmap 5 word -> (word -> option byte) -> Model -> Prop.
Definition K2r_t : Type :=
alayout -> astate -> list Z -> world segs -> bvmap 5 word -> (word -> option byte) -> Model ->
sptr -> Z -> Z -> list (Z * Z * Z) ->
sptr -> alayout -> astate -> world segs -> bvmap 5 word -> (word -> option byte) -> Model -> Prop.
Definition Knr_t : Type :=
alayout -> astate -> list Z -> world segs -> bvmap 5 word -> (word -> option byte) -> Model ->
Z -> list (Z * Z * Z) ->
astate -> world segs -> bvmap 5 word -> (word -> option byte) -> Model -> Prop.

(* ---------------------------------------------------------------------------- *)
(* 1. The walk records.                                                          *)

(* realloc(p, n): entry -> Allocate's call -> (Allocate) -> the copy routine's call -> (copy) -> Deallocate's call ->
   (Deallocate) -> return; and Allocate's NULL return -> return. *)
Record wrap_realloc_walk_cf (ARX : ARXh_t segs) (K1 : K1r_t) (K2 K3 : K2r_t) : Prop := {
(* S1 (RGtop seg_pre). The interceptor's entry (cf_pc_wrap_realloc) -> Reallocate's `jal Allocate`; the entry step
   free_cf PNull is realized on the way. At the call: Allocate's pre at Hp under its model premises (which
   rmodel_ok_cf_wf supplies), the stack window inside the caller's, the keeps across the walk's own instructions,
   errno, and K1. The stack room ly_bot ly + 4096 < spZ regs is acall_prefix_cf's and the errbuf placement
   xs_placed_cf ly S acall_xs_cf's (see section 2). *)
rw_pre : forall ly S Hp W regs mem md p n_old n ch,
  rentry_cf ly S Hp W regs mem md p n_old n ch -> ly_bot ly + 4096 < spZ regs -> xs_placed_cf ly S ->
  YGcfRmodel.rpre_cfr B S n -> 0 <= n < nmax ->
  amreal segs (free_cf PNull (rtr_cf ly regs ch) S) W (cfg_at segs cf_pc_wrap_realloc regs mem md)
  (fun r W1 c1 => exists inst so bp regsA memA mdA,
    c1 = cfg_at segs cf_pc_allocate regsA memA mdA /\
    (YGcfRmodel.rpre_cfr B (snd r) n -> blocks_bytes (snd r) + n <= LIVE_MAX -> admits (as_universe B) (rtr_cf ly regs ch) (snd r) ->
     malloc_apre_cf segs B nmax al atp acf ARX Hp inst so bp ly (snd r) W1 regsA memA mdA n (rtr_cf ly regs ch)) /\
    wle W W1 /\ same_io md mdA /\ RGtop.rin regs (spZ regsA) AllocG.AFSTACK_G /\
    ikeep_cf segs B ly S regs W mem W1 memA /\ errno_kept_cf B mem memA /\
    K1 ly S Hp W regs mem md p n_old n ch (snd r) W1 regsA memA mdA);
(* S2a (RGtop seg_mid_a). Allocate's return with a block q (raZ regsA) -> the copy routine's entry (cf_pc_memcpy)
   with dst = q, src = p, len = min (req_size n_old) n. *)
rw_mid_a : forall ly S Hp W regs mem md p n_old n ch S1 W1 inst so bp regsA memA mdA q ly2 S2 W2 regs2 mem2 md2,
  rentry_cf ly S Hp W regs mem md p n_old n ch ->
  K1 ly S Hp W regs mem md p n_old n ch S1 W1 regsA memA mdA ->
  malloc_apre_cf segs B nmax al atp acf ARX Hp inst so bp ly S1 W1 regsA memA mdA n (rtr_cf ly regs ch) ->
  malloc_apost_cf segs B ARX Hp inst ly S1 W1 regsA memA mdA
    (fun a => q <> PNull /\ sptr_addr B ly2 q <= a < sptr_addr B ly2 q + req_size n) ly2 S2 W2 regs2 mem2 md2 ->
  getr regs2 10 = w64 (sptr_addr B ly2 q) -> q <> PNull -> In (q, n) (blocks S2) -> q <> p -> qtight S2 ->
  In (p, n_old) (blocks S1) -> In (p, n_old) (blocks S2) -> rpreD_free_cf B S2 n_old ->
  SRr segs W2 (cfg_at segs (raZ regsA) regs2 mem2 md2)
  (fun W3 c3 => exists regsM memM mdM,
    c3 = cfg_at segs cf_pc_memcpy regsM memM mdM /\
    ReallocG.rmemcpy_pre segs W3 regsM memM (sptr_addr B ly2 q) (sptr_addr B ly p) (Z.min (req_size n_old) n) /\
    (forall i, 0 <= i < Z.min (req_size n_old) n ->
     aview segs (w_H W3) memM (sptr_addr B ly p + i) = aview segs (w_H W) mem (sptr_addr B ly p + i)) /\
    (forall a, sptr_addr B ly2 q <= a < sptr_addr B ly2 q + req_size n -> 0 <= a < 2 ^ 64 /\ ~ ascratch B ASTACK regs a) /\
    same_io md2 mdM /\ RGtop.rkeep segs B regs W2 mem2 W3 memM /\
    errno_kept_cf B mem2 memM /\ 
    K2 ly S Hp W regs mem md p n_old n ch q ly2 S2 W3 regsM memM mdM);
(* The copy routine (REAL(memcpy), reached at cf_pc_memcpy): ReallocG.amemcpy_realizes (ReallocG.v:243-251) at that
   pc, with the overlay normal form kept. *)
rw_memcpy : forall (W : world segs) regs mem md d s n,
  ReallocG.rmemcpy_pre segs W regs mem d s n ->
  SRr segs W (cfg_at segs cf_pc_memcpy regs mem md)
  (fun W' c' => (W' = W /\ exists regs' mem' md',
    c' = cfg_at segs (raZ regs) regs' mem' md' /\ aregs_preserved regs regs' /\ same_but_materialized md md' /\
    (forall i, 0 <= i < n -> aview segs (w_H W) mem' (d + i) = aview segs (w_H W) mem (s + i)) /\
    (forall x : word, ~ (d <= bv_unsigned x < d + n) -> mem' x = mem x) /\
    (forall a, apresent (w_H W) mem a -> apresent (w_H W) mem' a)));
(* S2b (RGtop seg_mid_b). The copy routine's return (raZ regsM) -> Reallocate's `jal Deallocate`: Deallocate's pre
   on the old block at Hp (fpre := True). *)
rw_mid_b : forall ly S Hp W regs mem md p n_old n ch q ly2 S2 W3 regsM memM mdM regs3 mem3 md3,
  rentry_cf ly S Hp W regs mem md p n_old n ch ->
  K2 ly S Hp W regs mem md p n_old n ch q ly2 S2 W3 regsM memM mdM ->
  In (p, n_old) (blocks S2) -> rpreD_free_cf B S2 n_old -> admits (as_universe B) (rtr_cf ly regs ch) S2 ->
  ly_bot ly + 4096 < spZ regs ->
  aregs_preserved regsM regs3 -> same_but_materialized mdM md3 ->
  (forall i, 0 <= i < Z.min (req_size n_old) n ->
   aview segs (w_H W3) mem3 (sptr_addr B ly2 q + i) = aview segs (w_H W3) memM (sptr_addr B ly p + i)) ->
  (forall x : word, ~ (sptr_addr B ly2 q <= bv_unsigned x < sptr_addr B ly2 q + Z.min (req_size n_old) n) ->
   mem3 x = memM x) ->
  (forall a, apresent (w_H W3) memM a -> apresent (w_H W3) mem3 a) ->
  SRr segs W3 (cfg_at segs (raZ regsM) regs3 mem3 md3)
  (fun W4 c4 => exists inst so bp regsD memD mdD,
    c4 = cfg_at segs cf_pc_deallocate regsD memD mdD /\
    realloc_dpre_cf ARX Hp inst so bp ly2 S2 W4 regsD memD mdD p n_old (rtr_cf ly regs ch) /\
    same_io md3 mdD /\ RGtop.rin regs (spZ regsD) DeallocG.DFSTACK_G /\
    RGtop.rkeep segs B regs W3 mem3 W4 memD /\ RGtop.rwin segs regs W4 memD /\
    errno_kept_cf B mem3 memD /\
    K3 ly S Hp W regs mem md p n_old n ch q ly2 S2 W4 regsD memD mdD);
(* S3 (RGtop seg_ret). Deallocate's return (raZ regsD) -> the interceptor's return (raZ regs), a0 = q. Deallocate's
   post is at a ghost set Hp' (the bridge uses Hp' := Hp); the segment carries that ARX to the return. *)
rw_ret : forall ly S Hp Hp' W regs mem md p n_old n ch q ly2 S2 W4 inst so bp regsD memD mdD ly3 S3 W5 regs5 mem5 md5,
  rentry_cf ly S Hp W regs mem md p n_old n ch ->
  K3 ly S Hp W regs mem md p n_old n ch q ly2 S2 W4 regsD memD mdD ->
  realloc_dpre_cf ARX Hp inst so bp ly2 S2 W4 regsD memD mdD p n_old (rtr_cf ly regs ch) ->
  free_dpost_cf segs B ARX Hp' inst ly2 S2 W4 regsD memD mdD
    (fun a => p <> PNull /\ sptr_addr B ly2 p <= a < sptr_addr B ly2 p + req_size n_old) ly3 S3 W5 regs5 mem5 md5 ->
  qtight S3 ->
  SRr segs W5 (cfg_at segs (raZ regsD) regs5 mem5 md5)
  (fun W' c' => exists regs' mem' md',
    c' = cfg_at segs (raZ regs) regs' mem' md' /\ aregs_preserved regs regs' /\
    getr regs' 10 = w64 (sptr_addr B ly2 q) /\
    ARX Hp' inst ly3 S3 W' mem' md' /\ same_io md5 md' /\
    RGtop.rkeep segs B regs W5 mem5 W' mem' /\ RGtop.rwin segs regs W' mem' /\
    errno_kept_cf B mem5 mem');
(* S4 (RGtop seg_nret). Allocate's return with PNull (raZ regsA) -> the interceptor's return, a0 = 0: errno :=
   ENOMEM and the out-of-memory byte. (RGtop's image premise as_errno B = as_tp B - 0xa4 is the walk's own.) *)
rw_nret : forall ly S Hp W regs mem md p n_old n ch S1 W1 inst so bp regsA memA mdA ly2 S2 W2 regs2 mem2 md2,
  rentry_cf ly S Hp W regs mem md p n_old n ch ->
  K1 ly S Hp W regs mem md p n_old n ch S1 W1 regsA memA mdA ->
  malloc_apre_cf segs B nmax al atp acf ARX Hp inst so bp ly S1 W1 regsA memA mdA n (rtr_cf ly regs ch) ->
  malloc_apost_cf segs B ARX Hp inst ly S1 W1 regsA memA mdA
    (fun a => PNull <> PNull /\ sptr_addr B ly2 PNull <= a < sptr_addr B ly2 PNull + req_size n) ly2 S2 W2 regs2 mem2 md2 ->
  getr regs2 10 = w64 (sptr_addr B ly2 PNull) -> qtight S2 ->
  val_mem segs (mrestrict (w_H W2) mem2) (as_oom_byte B) 1 1 ->
  In (p, n_old) (blocks S1) -> In (p, n_old) (blocks S2) ->
  SRr segs W2 (cfg_at segs (raZ regsA) regs2 mem2 md2)
  (fun W' c' => exists regs' mem' md',
    c' = cfg_at segs (raZ regs) regs' mem' md' /\ aregs_preserved regs regs' /\ getr regs' 10 = w64 0 /\
    ARX Hp inst ly2 S2 W' mem' md' /\ same_io md2 md' /\
    RGtop.rkeep segs B regs W2 mem2 W' mem' /\ RGtop.rwin segs regs W' mem' /\
    val_mem segs (mrestrict (w_H W') mem') (as_errno B) 4 12 /\
    val_mem segs (mrestrict (w_H W') mem') (as_oom_byte B) 1 1)
}.

(* realloc(NULL, n): entry -> asan_realloc's NULL-input `jal Allocate` -> (Allocate) -> return (RGtop's
   rg_realloc_null split into seg_npre / seg_npost). *)
Record wrap_realloc_null_walk_cf (ARX : ARXh_t segs) (Kn : Knr_t) : Prop := {
(* S5 (RGtop seg_npre). The interceptor's entry, a0 = 0 -> asan_realloc's `jal Allocate`; free_cf PNull realized on
   the way. The stack room and the errbuf placement as in S1. *)
rwn_pre : forall ly S Hp W regs mem md n ch,
  rnentry_cf ly S Hp W regs mem md n ch -> ly_bot ly + 4096 < spZ regs -> xs_placed_cf ly S ->
  YGcfRmodel.rpre_cfr B S n -> 0 <= n < nmax ->
  amreal segs (free_cf PNull (rtr_cf ly regs ch) S) W (cfg_at segs cf_pc_wrap_realloc regs mem md)
  (fun r W1 c1 => exists inst so bp regsA memA mdA,
    c1 = cfg_at segs cf_pc_allocate regsA memA mdA /\
    (YGcfRmodel.rpre_cfr B (snd r) n -> blocks_bytes (snd r) + n <= LIVE_MAX -> admits (as_universe B) (rtr_cf ly regs ch) (snd r) ->
     malloc_apre_cf segs B nmax al atp acf ARX Hp inst so bp ly (snd r) W1 regsA memA mdA n (rtr_cf ly regs ch)) /\
    wle W W1 /\ same_io md mdA /\ RGtop.rin regs (spZ regsA) AllocG.AFSTACK_G /\
    ikeep_cf segs B ly S regs W mem W1 memA /\ errno_kept_cf B mem memA /\
    Kn ly S Hp W regs mem md n ch (snd r) W1 regsA memA mdA);
(* S6 (RGtop seg_npost). Allocate's return (raZ regsA) with a block or PNull -> the interceptor's return, a0 = the
   result; on PNull errno := ENOMEM and the out-of-memory byte, on a block errno kept. *)
rwn_post : forall ly S Hp W regs mem md n ch S1 W1 inst so bp regsA memA mdA q ly2 S2 W2 regs2 mem2 md2,
  rnentry_cf ly S Hp W regs mem md n ch ->
  Kn ly S Hp W regs mem md n ch S1 W1 regsA memA mdA ->
  malloc_apre_cf segs B nmax al atp acf ARX Hp inst so bp ly S1 W1 regsA memA mdA n (rtr_cf ly regs ch) ->
  malloc_apost_cf segs B ARX Hp inst ly S1 W1 regsA memA mdA
    (fun a => q <> PNull /\ sptr_addr B ly2 q <= a < sptr_addr B ly2 q + req_size n) ly2 S2 W2 regs2 mem2 md2 ->
  getr regs2 10 = w64 (sptr_addr B ly2 q) -> qtight S2 ->
  (q = PNull -> val_mem segs (mrestrict (w_H W2) mem2) (as_oom_byte B) 1 1) ->
  (q <> PNull -> In (q, n) (blocks S2)) ->
  SRr segs W2 (cfg_at segs (raZ regsA) regs2 mem2 md2)
  (fun W' c' => exists regs' mem' md',
    c' = cfg_at segs (raZ regs) regs' mem' md' /\ aregs_preserved regs regs' /\
    getr regs' 10 = w64 (sptr_addr B ly2 q) /\
    ARX Hp inst ly2 S2 W' mem' md' /\ same_io md2 md' /\
    RGtop.rkeep segs B regs W2 mem2 W' mem' /\ RGtop.rwin segs regs W' mem' /\
    (q = PNull -> val_mem segs (mrestrict (w_H W') mem') (as_errno B) 4 12 /\
                  val_mem segs (mrestrict (w_H W') mem') (as_oom_byte B) 1 1) /\
    (q <> PNull -> errno_kept_cf B mem2 mem'))
}.

(* ---------------------------------------------------------------------------- *)
(* 2. The premises realloc needs beyond the malloc / free bridges'.              *)

(* ARX gives qmeter_cf where the unit's hull admission holds: Deallocate's premise rpreD_free_cf at the state after the
   inner malloc (YGcfMallocCompose.v:277) needs qmeter_cf there, and RGtop.rmodel_ok at the instance
   (YGcfRmodel.rmodel_ok_cf_wf) gives rpreD_cfr only. At the layer's call-site relation it is YGcfInstBase.ARXq_cf_qm
   (:507, the hull field round); the composition supplies cf_hull_ok at that state from the caller's post admission. *)
Definition ARX_qmh (ARX : ARXh_t segs) : Prop :=
forall Hp inst ly S W mem md, ARX Hp inst ly S W mem md -> cf_hull_ok S -> qmeter_cf S.

(* The stack room at the interceptor's entry: the engine's acall_pre_cf conjunct ly_bot ly + ACALL_PREFIX < spZ regs,
   ACALL_PREFIX := 4096 (a Theorem Labs lane, the internal file ACALL-PREFIX.md; a Theorem Labs lane 2026-10-29 16:00Z). It is on this base (YG0dcf.v:61,
   since d48cd401d143), so acall_prefix_cf is the projection of acall_pre_cf's conjunct (lane R's
   YGcfInstRealloc.acall_prefix_cf_ok). *)
Definition acall_prefix_cf : Prop :=
forall ly S Hp W regs mem md ch, acall_pre_cf segs B ly S Hp W regs mem md ch -> ly_bot ly + 4096 < spZ regs.

(* The errbuf slot's placement at the interceptor's entry: the S1 / S5 walks build Allocate's pre at the consumer's
   ARX (YGcfDIface.ARXs_cf's last conjunct, YGcfDIface.v:77), and acall_pre_cf does not state it. NOT vacuous: it holds
   once xs_placed_cf is ARcf's appended-last field (a Theorem Labs lane, 2026-10-29 14:41Z / 16:43Z, landing 1), with its
   projection xs_placed_of_ARcf : ARcf segs B ly S Hp W mem md -> xs_placed_cf ly S; acall_pre_cf's first conjunct is
   ARcf, so acall_xs_cf is then one line (destruct acall_pre_cf; apply xs_placed_of_ARcf). *)
Definition acall_xs_cf : Prop :=
forall ly S Hp W regs mem md ch, acall_pre_cf segs B ly S Hp W regs mem md ch -> xs_placed_cf ly S.

(* ARX gives batch_room_cf: free's model post (ml_free_cf, YG03dcf.v:428: blocks, frames) at the state after the inner
   malloc needs it, and the inner malloc may use it up (YGcfAmx2.realloc_cf_atok takes it as a premise, :127).
   YGcfDIface.ARXs_cf's seventh conjunct (YGcfDIface.v:77). *)
Definition ARX_br (ARX : ARXh_t segs) : Prop :=
forall Hp inst ly S W mem md, ARX Hp inst ly S W mem md -> batch_room_cf S.

(* errno's four bytes are a 64-bit address range: the copy routine's raw frame keeps every byte outside its
   destination, and the destination (the new block) is outside ascratch's errno range only as unwrapped numbers.
   An image-symbol fact: api_env's first conjunct (YCbq.v:809; TfibLib's tl_errno, YCeg.v:43) with
   kLowMemEnd <= 2 ^ 64. *)
Definition errno_word_cf : Prop := 0 <= as_errno B /\ as_errno B + 4 <= 2 ^ 64.

(* ---------------------------------------------------------------------------- *)
(* 2b. Helpers: the leaf's byte forms, addresses across a layout step, the owned  *)
(*     set across realloc's two allocator calls, and Deallocate's two pres.       *)

(* val_mem on the restricted memory is rd32 / the byte on the view (aview reads mbyte of the restriction). *)
Lemma vm_rd32_cf : forall (H : word -> bool) mem a v, val_mem segs (mrestrict H mem) a 4 v -> rd32 (aview segs H mem) a v.
Proof.
intros H mem a v V k Hk. unfold aview. rewrite (V k Hk). cbn [option_map]. f_equal.
rewrite Z_to_bv_unsigned. apply bv_wrap_small. assert (E : bv_modulus 8 = 256) by reflexivity. rewrite E.
unfold le_byte. apply Z.mod_pos_bound. lia.
Qed.

Lemma vm_byte1_cf : forall (H : word -> bool) mem a, val_mem segs (mrestrict H mem) a 1 1 -> aview segs H mem a = Some 1.
Proof.
intros H mem a V. pose proof (V 0%nat ltac:(lia)) as V0. cbn [Z.of_nat] in V0. rewrite Z.add_0_r in V0.
unfold aview. rewrite V0. cbn [option_map]. rewrite Z_to_bv_unsigned. reflexivity.
Qed.

(* A live block's address is kept by a layout step (YG0s.sptr_addr_le, as AR_layout_law_ok_cf's USR, YG0scf.v:585). *)
Lemma sptr_addr_block_cf : forall U ly ly' S p n, Wf_cf U S -> In (p, n) (blocks S) ->
layout_le (length (st_secs S)) ly ly' -> sptr_addr B ly' p = sptr_addr B ly p.
Proof.
intros U ly ly' S p n WF Hb LE.
destruct (proj1 (In_blocks S p n) Hb) as (k & Hk & _ & Hu & _). subst p.
apply (YG0s.sptr_addr_le B ly ly' (length (st_secs S))); [exact LE|].
pose proof (proj1 (Forall_forall _ _) (wfc_chunks _ _ _ _ _ WF) k Hk) as [_ C]. unfold ck_user.
destruct (ck_beg k) as [|o|r o|c p0]; cbn; try exact I.
destruct C as (_ & _ & sm & Hsm & _). apply nth_error_Some. rewrite Hsm. discriminate.
Qed.

Lemma pw_snoc_cf {X : Type} (R : X -> X -> Prop) : forall l y x, pairwise R (l ++ [y]) -> In x l -> R x y.
Proof.
induction l as [|a t IH]; intros y x P Hx; [destruct Hx|].
cbn [app pairwise] in P. destruct P as [F P].
destruct Hx as [<-|Hx].
- apply (proj1 (Forall_forall _ _) F y). apply in_or_app. right. left. reflexivity.
- exact (IH y x P Hx).
Qed.

Lemma realloc_hp_nn_cf : forall ly p q Hp, q <> PNull ->
YGcfRealloc.realloc_hp_cf B ly p q Hp = remove Z.eq_dec (sptr_addr B ly p) Hp.
Proof. intros ly p q Hp Hq. destruct q; [exfalso; exact (Hq eq_refl) | reflexivity | reflexivity | reflexivity]. Qed.

(* The owned set at the middle state of realloc(p, n). At one layout L: if the middle state's chunks are the first
   state's plus the new block's, the first state's live blocks stay live in the middle and the third state's live
   blocks were live in the middle, with the frames unchanged and the new block still live in the third state, then an
   owned byte of the middle state is owned in the first or in the third state. (An owned byte of the middle state that
   is a client byte in the first or third state is a client byte in the middle; an extent of the middle state is the
   first state's or the new block's, which the third state keeps.) *)
Lemma aowned_mid_cf : forall L S S2 S3 q n a,
(forall k, In k (st_chunks S2) -> In k (st_chunks S) \/ (ck_user k = q /\ ck_req k = n)) ->
(forall b, In b (blocks S) -> In b (blocks S2)) -> frames S2 = frames S ->
In (q, n) (blocks S3) -> (forall b, In b (blocks S3) -> In b (blocks S2)) -> frames S3 = frames S2 ->
aowned B L S2 a -> ~ aowned B L S a -> ~ aowned B L S3 a -> False.
Proof.
intros L S S2 S3 q n a CH BL FR QB3 BL3 FR3 O2 NA NA3.
unfold aowned in O2, NA, NA3.
assert (CL : forall X, (forall b, In b (blocks X) -> In b (blocks S2)) -> frames X = frames S2 ->
  aclient_byte B L X a -> aclient_byte B L S2 a).
{ intros X HB HF [(k & Hk & Hs & Ha) | (cp0 & Hcp & Ha)].
  - left. assert (Hb : In (ck_user k, ck_req k) (blocks X)) by (apply In_blocks; exists k; auto).
    destruct (proj1 (In_blocks S2 _ _) (HB _ Hb)) as (k' & Hk' & Hs' & Hu' & Hr').
    exists k'. split; [exact Hk'|]. split; [exact Hs'|]. unfold ck_n in *. rewrite Hu', Hr'. exact Ha.
  - right. exists cp0. rewrite <- HF. split; assumption. }
destruct O2 as [BASE NC2].
assert (NCS : ~ aclient_byte B L S a) by (intros C; exact (NC2 (CL S BL (eq_sym FR) C))).
assert (NCS3 : ~ aclient_byte B L S3 a) by (intros C; exact (NC2 (CL S3 BL3 FR3 C))).
assert (BS : forall e, In e (sec_extents L S2) -> In e (sec_extents L S) \/ In e (sec_extents L S3)).
{ intros e He. unfold sec_extents in He |- *. apply in_flat_map in He as (k & Hk & He).
  destruct (CH k Hk) as [Hk0 | (Hu & Hr)].
  - left. apply in_flat_map. exists k. split; [exact Hk0 | exact He].
  - right. destruct (proj1 (In_blocks S3 q n) QB3) as (k3 & Hk3 & _ & Hu3 & Hr3).
    apply in_flat_map. exists k3. split; [exact Hk3|].
    assert (EU : padd (ck_beg k3) (rz_size n) = padd (ck_beg k) (rz_size n)).
    { unfold ck_user, ck_rz in Hu, Hu3. rewrite Hr in Hu. rewrite Hr3 in Hu3. congruence. }
    rewrite Hr3. rewrite Hr in He.
    revert He EU. destruct (ck_beg k) as [|o|r o|c0 p0]; cbv beta iota; intros He EU; try (exfalso; exact He).
    cbn [padd] in EU. revert EU. destruct (ck_beg k3) as [|o3|r3 o3|c3 p3]; cbn [padd]; intros EU; try discriminate EU.
    injection EU as Er _. subst r3. cbv beta iota. exact He. }
destruct BASE as [O | [O | [O | [O | O]]]].
- apply NA. split; [left; exact O | exact NCS].
- apply NA. split; [right; left; exact O | exact NCS].
- apply NA. split; [right; right; left; exact O | exact NCS].
- apply Exists_exists in O as (e & He & Ha). destruct (BS e He) as [H0|H0].
  + apply NA. split; [right; right; right; left; apply Exists_exists; exists e; split; assumption | exact NCS].
  + apply NA3. split; [right; right; right; left; apply Exists_exists; exists e; split; assumption | exact NCS3].
- apply Exists_exists in O as (e & He & Ha). apply in_app_iff in He as [He | He].
  + apply NA. split; [|exact NCS]. right; right; right; right. apply Exists_exists. exists e.
    split; [apply in_app_iff; left; exact He | exact Ha].
  + apply in_app_iff in He as [He | He].
    * destruct (BS e He) as [H0|H0].
      -- apply NA. split; [|exact NCS]. right; right; right; right. apply Exists_exists. exists e.
         split; [apply in_app_iff; right; apply in_app_iff; left; exact H0 | exact Ha].
      -- apply NA3. split; [|exact NCS3]. right; right; right; right. apply Exists_exists. exists e.
         split; [apply in_app_iff; right; apply in_app_iff; left; exact H0 | exact Ha].
    * apply NA. split; [|exact NCS]. right; right; right; right. apply Exists_exists. exists e.
      split; [apply in_app_iff; right; apply in_app_iff; right; exact He | exact Ha].
Qed.

(* S2b's Deallocate pre (fpre := True) with the old base not hidden is the free bridge's. *)
Lemma realloc_dpre_free : forall ARX Hp inst so bp ly S W regs mem md p n tr,
realloc_dpre_cf ARX Hp inst so bp ly S W regs mem md p n tr -> ~ In (sptr_addr B ly p) Hp ->
free_dpre_cf segs B atpD ARX Hp inst so bp ly S W regs mem md p n tr.
Proof.
unfold realloc_dpre_cf, free_dpre_cf, DeallocG.dealloc_pre, fpre_hp_cf. intros. tauto.
Qed.

(* ---------------------------------------------------------------------------- *)
(* 3. The bridges.                                                               *)

(* realloc(NULL, n): YGcfRealloc.arealloc_null_realizes_cf at every ghost set, at the interceptor's entry
   (pa_realloc_null_cf's body, A/CfApiPreset.v:98-100). *)
Theorem arealloc_null_realizes_cf_of_parts : forall (ARX : ARXh_t segs) (Kn : Knr_t),
acall_prefix_cf -> acall_xs_cf -> nmax_cf_ok nmax -> ARX_ARcf segs B ARX -> ARX_xs segs ARX ->
(* field round 3 part 3b: the two image rows behind arodata_ok_cf at Allocate's entry, as the non-NULL bridge *)
relro_seg_t segs -> errno_relro_t B ->
aalloc_realizes_cf_em_m segs B nmax al atp acf ARX ->
wrap_realloc_null_walk_cf ARX Kn ->
forall Hp, YGcfRealloc.arealloc_null_realizes_cf segs B Hp cf_pc_wrap_realloc.
Proof.
intros ARX Kn HPFX HXSP HNM HAR HXS RS ER HAM [WNPRE WNPOST] Hp.
intros ly S W regs mem md n ch PRE _ H10 H11 Hn Hlive Htr. cbv beta in PRE |- *.
pose proof (aalloc_realizes_cf_em_of_m segs B nmax al atp acf ARX HAM) as HA.
assert (ENT : rnentry_cf ly S Hp W regs mem md n ch) by exact (conj PRE (conj H10 (conj H11 (conj Hn (conj Hlive Htr))))).
pose proof (HPFX ly S Hp W regs mem md ch PRE) as HBOT.
pose proof (HXSP ly S Hp W regs mem md ch PRE) as HXS0.
pose proof (rpre_cfr_of_pre segs B ly S Hp W regs mem md ch n PRE) as RP.
assert (HN : 0 <= n < nmax) by (unfold nmax_cf_ok in HNM; lia).
set (tr := call_trace ly cf_pc_realloc_ra0 regs ch) in *.
unfold ReallocP.realloc_null_tree_with.
eapply amreal_mbind; [exact (RGtop.rg_apath_gflag segs _ _ _ _ (WNPRE ly S Hp W regs mem md n ch ENT HBOT HXS0 RP HN))|].
intros [] S1 W1 c1 H1. cbv beta in H1.
destruct H1 as [(inst & so & bp & regsA & memA & mdA & Ec1 & APREi & WLE1 & IO1 & RIN1 & KP1 & ER1 & HKn) (trc1 & HP1 & HG1)].
subst c1. cbn [snd] in *.
destruct (YGcfRmodel.rmodel_ok_cf_wf B) as [MO1 MO2].
destruct (MO1 S n tr trc1 S1 RP Hn Hlive Htr HP1 HG1) as (UA1 & RA1 & BB1 & BL1 & SEC1 & AOX1).
pose proof (APREi RA1 BB1 UA1) as APR.
assert (XO : forall a, ~ aowned B ly S a -> ~ Exists (in_zr a) (xs_cf ly S) -> ~ AOXm_cf B ly S1 a).
{ intros a N1 N2 X. destruct (AOX1 ly a X) as [Y|Y]; [exact (N1 Y) | exact (N2 Y)]. }
(* Allocate, with arodata_ok_cf at its entry memory (part 3b / 3c), as in the non-NULL bridge *)
pose proof (acall_pre_cf_ro ly S Hp W regs mem md ch PRE) as HROa0.
assert (ROa : arodata_ok_cf segs B memA).
{ pose proof (amc_layout _ _ _ _ _ (proj1 (proj1 PRE))) as LOa.
  assert (STKa : ly_stk_lo ly + ASTACK <= spZ regs) by (destruct PRE as (_ & _ & _ & STK & _); exact STK).
  apply (arodata_frame_cf segs B (fun a => aowned B ly S a \/ ascratch B ASTACK regs a) mem memA); [| |exact HROa0].
  - intros x NX. exact (proj2 KP1 x (fun H => NX (or_introl H)) (fun H => NX (or_intror H))).
  - intros a Ha NO. destruct (relro_apart_cf segs B ly S Hp W mem md a (proj1 PRE) RS Ha NO) as (R & _ & NA0 & _).
    split; [unfold kImgLo, kImgEnd in R; lia|].
    intros [X|X]; [exact (NA0 X) | exact (relro_not_scratch_cf B ly ASTACK regs a LOa STKa ER Ha R X)]. }
eapply RGtop.rg_then_SRr; [exact (HA Hp inst so bp ly S1 W1 regsA memA mdA n tr APR ROa)|].
intros [q S2] W2 c2 [LEAF KEEP].
unfold malloc_aleaf_cf, AllocG.alloc_leaf in LEAF.
destruct LEAF as (ly2 & regs2 & mem2 & md2 & Ec2 & APO & A02 & LP2 & (trc2 & HP2 & HG2) & OOM).
subst c2. cbn [fst snd] in *.
destruct (KEEP _ _ _ _ eq_refl) as [ERA _].
pose proof APO as (ARX2 & LLE2 & WLE2 & CS2 & IO2 & FR2 & FR2w & PR2).
destruct (MO2 S n tr trc1 S1 trc2 q S2 RP Hn Hlive Htr HP1 HG1 HP2 HG2) as (_ & QB2 & _).
eapply SRr_mono; [exact (WNPOST ly S Hp W regs mem md n ch S1 W1 inst so bp regsA memA mdA q ly2 S2 W2 regs2 mem2 md2
  ENT HKn APR APO A02 LP2 OOM QB2)|].
intros W' c' WLE3 (regs' & mem' & md' & Ec' & CS' & A0' & ARX' & IO' & KP' & WN' & ENM' & ERK'). subst c'.
assert (XS : forall a, ~ ascratch B ASTACK regs a -> ~ ascratch B AllocG.AFSTACK_G regsA a)
  by (intros a NS X; exact (NS (RGtop.rg_scratch_in B regs regsA AllocG.AFSTACK_G a (proj1 RIN1) (proj2 RIN1) X))).
split.
- exists ly2, regs', mem', md'. cbn [fst snd].
  split; [reflexivity|].
  split.
  { split; [exact (HAR _ _ _ _ _ _ _ ARX')|].
    split; [exact (layout_le_trans _ _ ly ly ly2 SEC1 (layout_le_refl _ ly) LLE2)|].
    split; [eapply wle_trans; [exact WLE1|]; eapply wle_trans; [exact WLE2 | exact WLE3]|].
    split; [exact CS'|].
    split; [exact (RGtop.rg_same_io_trans _ _ _ (RGtop.rg_same_io_trans _ _ _ IO1 IO2) IO')|].
    split; [|exact WN'].
    intros a Ha NA NA2 NS NE.
    assert (NX0 : ~ Exists (in_zr a) (xs_cf ly S)) by (intros X; apply NE; right; apply Exists_app; left; exact X).
    assert (NX2 : ~ Exists (in_zr a) (xs_cf ly2 S2)) by (intros X; apply NE; right; apply Exists_app; right; exact X).
    rewrite (proj1 KP' a Ha NS).
    rewrite (FR2 a Ha (XO a NA NX0) ltac:(intros [X|X]; [exact (NA2 X) | exact (NX2 X)]) (XS a NS)
      ltac:(intros X; apply NE; left; exact X)).
    exact (proj1 KP1 a Ha NA NS). }
  split; [exact A0'|]. split; [exact LP2|].
  split; [intros EQ; destruct (ENM' EQ) as [ER0 OM0]; exact (conj (vm_rd32_cf _ _ _ _ ER0) (vm_byte1_cf _ _ _ OM0))|].
  split; [exact (HXS _ _ _ _ _ _ _ ARX')|].
  split; [intros Hq i Hi; rewrite (ERK' Hq i Hi), (ERA Hq i Hi); exact (ER1 i Hi)|].
  intros x NA NA2 NS NE.
    assert (NX0 : ~ Exists (in_zr (bv_unsigned x)) (xs_cf ly S)) by (intros X; apply NE; right; apply Exists_app; left; exact X).
    assert (NX2 : ~ Exists (in_zr (bv_unsigned x)) (xs_cf ly2 S2)) by (intros X; apply NE; right; apply Exists_app; right; exact X).
    rewrite (proj2 KP' x NS).
    rewrite (FR2w x (XO _ NA NX0) ltac:(intros [X|X]; [exact (NA2 X) | exact (NX2 X)]) (XS _ NS)
      ltac:(intros X; apply NE; left; exact X)).
    exact (proj2 KP1 x NA NS).
- intros EQ. subst q. exists S1, trc1, trc2. exact (conj HP1 (conj HG1 (conj HP2 HG2))).
Qed.
End R.

End J.
End G.
