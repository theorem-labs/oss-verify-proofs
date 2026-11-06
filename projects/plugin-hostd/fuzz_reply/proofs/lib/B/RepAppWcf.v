(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: from proofs/cgif/cgif_file_fuzzer/lib/RepAppWcf.v (commit f01d79f3fb5, cf refill round 3; file sha256 42338b9c3785) onto plugin-hostd/fuzz_reply's asan image (unstripped fuzz_reply.asan, sha256 d751b179ea49; pin 42c58610e125); module paths changed; its 54 image addresses moved by function pairs the comparison kit cmpkit 86da41d3ef68 calls the same code (strictcmp3 65688e94214a, by funcpair_reply 6963bc4a94fc on the cgif twin ce511d541cda; 79 port_addr_check e55e1b52a8a0 MAPS predictions, each code one re-derived by the pair, each data one a pc-relative target of both paired functions; 0 code pcs the tool read as sizes, by the pair), and 5 pcs named in comments; 6 hand maps (resolve-run-f01d79f3fb5.tsv (sha256 ba54f3af32ab; internal record), each with its evidence: pinned image bytes, YImgTop, the unit AF twin); no other numeral changed. *)
(* Theorem Labs, 2026-10-30 (a Theorem Labs lane, slice F4 of a Theorem Labs lane's class-full report walk, the walk itself):
   __asan::AppendToErrorMessageBuffer (0x56418) of cgif_file_fuzzer's asan-ubsan image (pin 1c29845fe605)
   realizes the model step errb_append_cf (YG00cf.v:133): append_ok_w : RepIFcf.append_spec_cf B.
   rule 24: proves function __asan::AppendToErrorMessageBuffer (reuse search: ossv proof index v5 built
   2026-10-30T01:54:20Z and 02:28:20Z over main / ossv/recipes / ossv/candidates /
   release/pau-projects-recipes plus the delivered package and the live cold/* working heads;
   `proof-index VSNPrintf Printf SharedPrintfCode AppendNumber AppendToErrorMessageBuffer MmapOrDie`
   2026-10-30T02:25:54Z exit 0 and `proof-index UnmapOrDie internal_memset internal_memcpy
   internal_strlen GetNamedMappingFd IncreaseTotalMmap` 2026-10-30T02:55Z exit 3; 0 released lemma(s) for
   every name; rule-24 check RepLookupCheck CONFIRM, nothing reusable: every cgif_file_fuzzer hit is a
   `by address` row of the YB1q.v / YB1w.v decode and symbol-name tables). *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s YO0d.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YP0j.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YN3v YI04.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YK04 YA0i YA0n YA0o YA0p YA0q.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0v YG0n YG0d.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import YB1v YB1q YB1t YF0l YF0m YF0x YFl0.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import YFff RepMemKcf YFel YFeq.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require YK0v YK13 YK02 YGcfXs.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require RepReallocD RepAppRcf.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable.Z Require Placement.
From LinuxProcessSemantics.LinuxProcessSem.Sys.Mm Require Mmap.
(* stdpp, through the LPS modules, shadows several list names; the lemmas here are Stdlib's. *)
From Stdlib Require Import List.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.
Set Printing Depth 100. Set Printing Width 200.

(* ---------------------------------------------------------------------------------------------------------------- *)
(* 1. The decode table of the function (0x56418 .. 0x566e0, 179 four-byte instructions).                            *)
Definition tbl_app_build : ctable := build_table tfibsegs 0x56418 179%nat TEmpty.
Definition tbl_app : ctable := Eval vm_compute in tbl_app_build.
Lemma tbl_app_eq : tbl_app = tbl_app_build.
Proof. vm_cast_no_check (@eq_refl ctable tbl_app). Qed.
Lemma tbl_app_ok : table_ok tfibsegs tbl_app.
Proof. rewrite tbl_app_eq. unfold tbl_app_build. apply build_table_ok0. cbv. discriminate. Qed.

(* ---------------------------------------------------------------------------------------------------------------- *)
(* 2. The seeds.  Atoms: 0..31 the entry registers (a0 = the string p, sp = atom 2), 32 data, 33 capacity, 34 size. *)
Definition O_ : Z := 0xa5ea8.
Definition aDATA : nat := 32.
Definition aCAP : nat := 33.
Definition aSIZE : nat := 34.
Definition rSTK : YP09.region := YP09.mkRegion (Some 2%nat) (- 96) 0 (- 96) 0 [].
Definition rOP (ptr : Z) : YP09.region := YP09.mkRegion None O_ (O_ + 32) O_ (O_ + 32)
  [YP09.mkChunk O_ (CVal 8 (SLit ptr)); YP09.mkChunk (O_ + 16) (CVal 8 (SLit 0))].
Definition rOD : YP09.region := YP09.mkRegion None (O_ + 32) (O_ + 48) (O_ + 32) (O_ + 48)
  [YP09.mkChunk (O_ + 32) (CVal 8 (SOff aDATA 0)); YP09.mkChunk (O_ + 40) (CVal 8 (SOff aCAP 0))].
Definition rOS : YP09.region := YP09.mkRegion None (O_ + 48) (O_ + 56) (O_ + 48) (O_ + 56)
  [YP09.mkChunk (O_ + 48) (CVal 8 (SOff aSIZE 0))].
Definition rK : YP09.region := YP09.mkRegion None 0x103a0 (0x103a0 + 8) 0 0 [YP09.mkChunk 0x103a0 (CVal 8 (SLit 0xafffff00000fffff))].
Definition AFACTS : facts := mkFacts
  [ (2%nat, mkAF (TFIB_IMG_END + 512) (2 ^ 64 - 1) 4); (aSIZE, mkAF 0 (2 ^ 47 - 1) 0); (aCAP, mkAF 0 (2 ^ 47 - 1) 0) ] [] [].
Definition SS_A (ptr : Z) : sstate := mkSS 0x56418 sr_atoms [rSTK; rOP ptr; rOD; rOS; rK] None AFACTS.
Definition Eseed (regs : bvmap 5 word) (data cap size : Z) : env := Ereg regs [Z_to_bv 64 data; Z_to_bv 64 cap; Z_to_bv 64 size].

Section s. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Local Ltac reg_intro := unfold region_ok; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
Lemma seed_ok : forall (W : world tfibsegs) (regs : bvmap 5 word) (mem : word -> option byte) (ptr data cap size : Z),
  let H := w_H W in let m := mrestrict H mem in let sp := bv_unsigned (getr regs 2) in
  sp mod 16 = 0 -> TFIB_IMG_END + 512 <= sp -> (forall a, sp - 96 <= a < sp -> apresent H mem a) ->
  0 <= ptr < 2 ^ 64 -> 0 <= data < 2 ^ 64 -> 0 <= cap < 2 ^ 47 -> 0 <= size < 2 ^ 47 ->
  val_mem tfibsegs m O_ 8 ptr -> val_mem tfibsegs m (O_ + 16) 8 0 -> val_mem tfibsegs m (O_ + 32) 8 data ->
  val_mem tfibsegs m (O_ + 40) 8 cap -> val_mem tfibsegs m (O_ + 48) 8 size ->
  val_mem tfibsegs m 0x103a0 8 0xafffff00000fffff ->
  st_ok tfibsegs (Eseed regs data cap size) (SS_A ptr) (restrict (w_H W) (mkst regs (Z_to_bv 64 0x56418) mem (seg_rom tfibsegs))).
Proof.
intros W regs mem ptr data cap size. cbv zeta. intros Hal Hsp HPRES Hptr Hd Hc Hs V0 V16 V32 V40 V48 VK.
pose proof (u64_range (getr regs 2)) as Usp.
assert (E2 : forall ex, ew (Ereg regs ex) 2 = getr regs 2) by (intros ex; exact (ew_Ereg_nat regs ex 2 2%bv eq_refl)).
assert (E32 : forall a b c, ew (Ereg regs [a; b; c]) aDATA = a) by reflexivity.
assert (E33 : forall a b c, ew (Ereg regs [a; b; c]) aCAP = b) by reflexivity.
assert (E34 : forall a b c, ew (Ereg regs [a; b; c]) aSIZE = c) by reflexivity.
unfold Eseed.
unfold SS_A. rewrite restrict_mkst_fx. apply (entry_st_ok_full tfibsegs).
- apply regs_ok_Ereg.
- vm_compute. reflexivity.
- cbn [ms_mem mkst]. unfold rSTK, rOP, rOD, rOS, rK.
  apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]]]]].
  + unfold TFIB_IMG_END in Hsp. apply (region_ok_stack tfibsegs _ _ 2 (bv_unsigned (getr regs 2)) (- 96)).
    * rewrite E2. reflexivity.
    * lia.
    * lia.
    * intros a Ha. apply apresent_writable; [unfold TFIB_IMG_END; lia | apply HPRES; lia].
  + reg_intro. unfold O_. split; [lia|]. split; [lia|]. split; [intros o Ho; apply rw_writable; lia|].
    apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]].
    * eapply chunk_ok_val; [reflexivity | cbn; lia | cbn; lia | rewrite Z.add_0_l; exact V0].
    * eapply chunk_ok_val; [reflexivity | cbn; lia | cbn; lia | rewrite Z.add_0_l; exact V16].
  + reg_intro. unfold O_. split; [lia|]. split; [lia|]. split; [intros o Ho; apply rw_writable; lia|].
    apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]].
    * eapply chunk_ok_val; [cbn [sv_denot]; rewrite E32, (unsigned_lit_small data), Z.add_0_r by lia; reflexivity | cbn; lia | cbn; lia | rewrite Z.add_0_l; exact V32].
    * eapply chunk_ok_val; [cbn [sv_denot]; rewrite E33, (unsigned_lit_small cap), Z.add_0_r by lia; reflexivity | cbn; lia | cbn; lia | rewrite Z.add_0_l; exact V40].
  + reg_intro. unfold O_. split; [lia|]. split; [lia|]. split; [intros o Ho; apply rw_writable; lia|].
    apply Forall_cons; [|apply Forall_nil].
    eapply chunk_ok_val; [cbn [sv_denot]; rewrite E34, (unsigned_lit_small size), Z.add_0_r by lia; reflexivity | cbn; lia | cbn; lia | rewrite Z.add_0_l; exact V48].
  + reg_intro. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
    apply Forall_cons; [|apply Forall_nil].
    eapply chunk_ok_val; [reflexivity | cbn; lia | cbn; lia | rewrite Z.add_0_l; exact VK].
- apply pairwise_disjoint_of_extents. unfold rSTK, rOP, rOD, rOS, rK, extent_of_region. cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val].
  rewrite E2. cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj, O_. cbn [fst snd]. unfold TFIB_IMG_END in *. repeat split; lia.
- split; [|split; exact I]. cbn [AFACTS f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
  rewrite E2, E33, E34, (unsigned_lit_small cap), (unsigned_lit_small size) by lia.
  repeat split; first [lia | change (2 ^ 4) with 16; exact Hal | rewrite Z.pow_0_r, Z.mod_1_r; reflexivity].
Qed.

Lemma vm1_mbyte : forall (m : word -> option byte) a v, val_mem tfibsegs m a 1 v -> 0 <= v < 256 ->
  mbyte tfibsegs m a = Some (Z_to_bv 8 v).
Proof.
intros m a v H Hv. specialize (H 0%nat ltac:(lia)). rewrite Z.add_0_r in H. rewrite H.
rewrite le_byte_small by (cbn; lia). cbn [Z.of_nat Z.mul]. rewrite Z.shiftr_0_r. reflexivity.
Qed.

Lemma str_bytes : forall (m : word -> option byte) p (s : list Z),
  (forall i, (i < length s)%nat -> val_mem tfibsegs m (p + Z.of_nat i) 1 (nth i s 0) /\ 0 < nth i s 0 < 256) ->
  val_mem tfibsegs m (p + Z.of_nat (length s)) 1 0 ->
  ~ In (Z_to_bv 8 0) (map (Z_to_bv 8) s) /\
  (forall j, (j <= length (map (Z_to_bv 8) s))%nat ->
     mbyte tfibsegs m (p + Z.of_nat j) = Some (nth j (map (Z_to_bv 8) s ++ [Z_to_bv 8 0]) (Z_to_bv 8 0))).
Proof.
intros m p s HS HN. split.
- intros Hin. apply In_nth with (d := Z_to_bv 8 0) in Hin as (j & Hj & Ej). rewrite length_map in Hj.
  rewrite (map_nth (Z_to_bv 8) s 0 j) in Ej.
  destruct (HS j Hj) as [_ R]. apply (f_equal bv_unsigned) in Ej. rewrite !unsigned_lit_small8 in Ej by lia. lia.
- intros j Hj. rewrite length_map in Hj. destruct (Nat.lt_ge_cases j (length s)) as [L|L].
  + rewrite app_nth1 by (rewrite length_map; exact L).
    rewrite (map_nth (Z_to_bv 8) s 0 j).
    destruct (HS j L) as [V R]. apply vm1_mbyte; [exact V | lia].
  + assert (j = length s) as -> by lia. rewrite app_nth2 by (rewrite length_map; lia).
    rewrite length_map, Nat.sub_diag. cbn [nth]. apply vm1_mbyte; [exact HN | lia].
Qed.

(* The write zones of the walk: the window below the entry sp and the errbuf object. *)
Definition AZ (sp x : Z) : Prop := (sp - 512 <= x < sp) \/ (O_ <= x < O_ + 56).
Ltac fkeep HF BV2 KW :=
lazymatch type of HF with frame_of ?E ?rs ?m ?m' =>
assert (KW : forall x : word, ~ AZ (bv_unsigned (ew E 2)) (bv_unsigned x) -> m' x = m x)
by (let x := fresh "x" in let Hx := fresh "Hx" in let r := fresh "r" in let Hr := fresh "Hr" in
intros x Hx; apply (frame_of_outside E rs m m' x HF); intros r Hr;
cbn [ss_mem SS_A ss_after_stretch ss_after_call In] in Hr; unfold rSTK, rOP, rOD, rOS, rK in Hr; unfold AZ in Hx;
repeat (destruct Hr as [<-|Hr]; [cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi base_val]; unfold O_ in *; lia|]);
destruct Hr);
clear HF
end.

(* ---------------------------------------------------------------------------------------------------------------- *)
(* 3. Run tactics that also keep the growth of the visible memory (YFel.v's run_postG over the _sh runs).            *)
Lemma SRr_run_to_shG : forall W n stop E ss ss' st ms model Q,
  st_ok tfibsegs E ss (restrict (w_H W) ms) -> sym_run_toN_sh tfibsegs tbl_app n stop ss = (ss', st) ->
  run_postG W E ss ss' st ms model Q -> SRr tfibsegs W (mkCfg ms model) Q.
Proof.
intros W n stop E ss ss' st ms model Q HS Hrun Hk.
destruct (msteps_run_to_sh tfibsegs tbl_app tbl_app_ok n stop E ss ss' st _ HS Hrun) as (msr' & Hms & HS' & Hfr).
exact (SRr_of_restricted_chainG W E ss ss' st ms msr' model Q Hms HS' Hfr Hk).
Qed.
Lemma SRr_run_shG : forall W n E ss ss' st ms model Q,
  st_ok tfibsegs E ss (restrict (w_H W) ms) -> sym_runN_sh tfibsegs tbl_app n ss = (ss', st) ->
  run_postG W E ss ss' st ms model Q -> SRr tfibsegs W (mkCfg ms model) Q.
Proof.
intros W n E ss ss' st ms model Q HS Hrun Hk.
destruct (msteps_run_sh tfibsegs tbl_app tbl_app_ok n E ss ss' st _ HS Hrun) as (msr' & Hms & HS' & Hfr).
exact (SRr_of_restricted_chainG W E ss ss' st ms msr' model Q Hms HS' Hfr Hk).
Qed.
Lemma apresent_grows : forall (H : word -> bool) m m' a, mem_grows (mrestrict H m) (mrestrict H m') ->
  apresent H m a -> apresent H m' a.
Proof.
intros H m m' a G [Hh [b Hb]]. split; [exact Hh|].
assert (N : mrestrict H m' (Z_to_bv 64 a) <> None) by (apply G; unfold mrestrict; rewrite Hh, Hb; discriminate).
unfold mrestrict in N. rewrite Hh in N. destruct (m' (Z_to_bv 64 a)) as [b'|]; [exists b'; reflexivity | exfalso; apply N; reflexivity].
Qed.
Lemma ext_apart : forall (lo hi d n data cap : Z), 0 < cap -> data <= d -> d + n <= data + cap -> 0 <= n ->
  (forall i, 0 <= i < cap -> data + i < lo \/ hi <= data + i) -> hi <= d \/ d + n <= lo \/ hi <= lo.
Proof.
intros lo hi d n data cap Hc Hd Hn Hn0 HB.
destruct (Z_le_gt_dec hi lo); [right; right; lia|]. destruct (Z_le_gt_dec hi d); [left; lia|].
destruct (Z_le_gt_dec (d + n) lo); [right; left; lia|]. exfalso.
destruct (Z_le_gt_dec lo d).
- destruct (Z_lt_ge_dec d (data + cap)).
  + destruct (HB (d - data) ltac:(lia)); lia.
  + destruct (HB (cap - 1) ltac:(lia)); lia.
- destruct (HB (lo - data) ltac:(lia)); lia.
Qed.

Ltac srun_to HS stop :=
lazymatch type of HS with
| st_ok ?segs ?E ?ss (restrict (w_H ?W) ?ms) =>
let r := eval vm_compute in (sym_run_toN_sh segs tbl_app FUEL stop ss) in
lazymatch r with (?ss', ?st) =>
let Hrun := fresh "Hrun" in
assert (Hrun : sym_run_toN_sh segs tbl_app FUEL stop ss = (ss', st)) by (vm_compute; reflexivity);
eapply (SRr_run_to_shG W FUEL stop E ss ss' st ms _ _ HS Hrun); clear Hrun HS
end end.
Ltac srun HS :=
lazymatch type of HS with
| st_ok ?segs ?E ?ss (restrict (w_H ?W) ?ms) =>
let r := eval vm_compute in (sym_runN_sh segs tbl_app FUEL ss) in
lazymatch r with (?ss', ?st) =>
let Hrun := fresh "Hrun" in
assert (Hrun : sym_runN_sh segs tbl_app FUEL ss = (ss', st)) by (vm_compute; reflexivity);
eapply (SRr_run_shG W FUEL E ss ss' st ms _ _ HS Hrun); clear Hrun HS
end end.
Ltac after_run HS HF HG := cbv beta iota in HS; cbn [ms_mem mkst] in HF, HG; rewrite ?wvb_collapse.
(* Old atoms of a havoc'd environment, in the goal and in a hypothesis. *)
Ltac env_simp := repeat match goal with |- context [ew (havoc ?E ?k ?ws) ?i] =>
  rewrite (ew_havoc_old E k ws i) by (apply Nat.ltb_lt; reflexivity) end.
Ltac env_simp_in H := repeat match type of H with context [ew (havoc ?E ?k ?ws) ?i] =>
  rewrite (ew_havoc_old E k ws i) in H by (apply Nat.ltb_lt; reflexivity) end.
Lemma ew_seed32 : forall regs a b c, ew (Eseed regs a b c) 32 = Z_to_bv 64 a. Proof. reflexivity. Qed.
Lemma ew_seed33 : forall regs a b c, ew (Eseed regs a b c) 33 = Z_to_bv 64 b. Proof. reflexivity. Qed.
Lemma ew_seed34 : forall regs a b c, ew (Eseed regs a b c) 34 = Z_to_bv 64 c. Proof. reflexivity. Qed.
Lemma ew_seed_reg : forall regs a b c n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew (Eseed regs a b c) n = getr regs r.
Proof. intros regs a b c n r Hn. exact (ew_Ereg_nat regs _ n r Hn). Qed.
(* A register's value at a state, through zev; [fin] closes the arithmetic. *)
Ltac regv HS r v Hn fin :=
lazymatch type of HS with st_ok _ ?E ?ss (restrict ?H ?ms) =>
let e := eval vm_compute in (sr_get (ss_regs ss) r) in
assert (Hn : getr (ms_regs ms) r = Z_to_bv 64 v)
by (rewrite (st_ok_reg_denot H E ss ms r HS); change (sr_get (ss_regs ss) r) with e;
    apply bv_eq; rewrite (unsigned_lit_small v) by (unfold M64, O_ in *; lia);
    change (bv_unsigned (sv_denot E e) = v) with (U E e = v);
    rewrite U_zev by reflexivity; cbn [zev zalu_raw]; unfold rho_of; env_simp; fin)
end.

Ltac zfin A35 := rewrite ?A35, ?ew_seed32, ?ew_seed33, ?ew_seed34; unfold zcanon, M64; rewrite ?unsigned_lit_small by lia; rewrite ?Z.add_0_r;
  repeat match goal with |- context [?x mod 2 ^ 64] => rewrite (Z.mod_small x (2 ^ 64)) by lia end; try lia.

Ltac brnorm Hc A35 :=
  first [rewrite branch_geu_U in Hc | rewrite branch_ltu_U in Hc];
  rewrite !U_zev in Hc by reflexivity; cbn [zev zalu_raw] in Hc; unfold rho_of in Hc; env_simp_in Hc;
  rewrite ?A35, ?ew_seed32, ?ew_seed33, ?ew_seed34 in Hc; unfold zcanon, M64 in Hc;
  rewrite ?unsigned_lit_small in Hc by lia; rewrite ?Z.add_0_r in Hc;
  repeat match type of Hc with context [?x mod 2 ^ 64] => rewrite (Z.mod_small x (2 ^ 64)) in Hc by lia end.
Ltac brnorm2 Hc A1 A2 :=
  first [rewrite branch_geu_U in Hc | rewrite branch_ltu_U in Hc];
  rewrite !U_zev in Hc by reflexivity; cbn [zev zalu_raw] in Hc; unfold rho_of in Hc; env_simp_in Hc;
  rewrite ?A1, ?A2, ?ew_seed32, ?ew_seed33, ?ew_seed34 in Hc; unfold zcanon, M64 in Hc;
  rewrite ?unsigned_lit_small in Hc by lia; rewrite ?Z.add_0_r in Hc;
  repeat match type of Hc with context [?x mod 2 ^ 64] => rewrite (Z.mod_small x (2 ^ 64)) in Hc by lia end.
(* Old frame + a run's frame and growth: the new memory still agrees with the entry memory outside the zones. *)
Ltac step_frame E2 EQo PRo EQn PRn HF HG :=
  let KW := fresh "KW" in fkeep HF E2 KW; env_simp_in KW; rewrite E2 in KW;
  lazymatch type of EQo with forall x : word, ~ AZ ?sp (bv_unsigned x) -> ~ (?lo <= bv_unsigned x < ?hi) -> ?mo x = ?m0 x =>
  lazymatch type of PRo with forall a, apresent ?Hh ?m0' a -> apresent ?Hh' ?mo' a =>
  lazymatch type of HG with mem_grows (mrestrict _ ?mo2) (mrestrict _ ?mn) =>
  assert (PRn : forall a, apresent Hh m0' a -> apresent Hh mn a)
    by (let a := fresh "a" in let Ha := fresh "Ha" in intros a Ha; apply (apresent_grows _ _ _ _ HG), PRo, Ha);
  assert (EQn : forall x : word, ~ AZ sp (bv_unsigned x) -> ~ (lo <= bv_unsigned x < hi) -> mn x = m0 x)
    by (let x := fresh "x" in let H1 := fresh "H1" in let H2 := fresh "H2" in
        intros x H1 H2; rewrite (KW x H1); exact (EQo x H1 H2))
  end end end; clear KW HG EQo PRo.
(* The region side conditions of a stretch into the buffer: every region of the walk is the frame, the object or
   the ROM word, and the buffer is wholly below or above the stack window and off the image (SB1 / SB2). *)
Ltac hext E2 :=
  let r := fresh "r" in let Hr := fresh "Hr" in intros r Hr; cbn [ss_mem In] in Hr;
  repeat (destruct Hr as [<-|Hr]; [cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val]; env_simp; rewrite ?E2; unfold O_ in *; lia|]); destruct Hr.
Ltac hext64 E2 :=
  let r := fresh "r" in let a := fresh "a" in let Hr := fresh "Hr" in let Ha := fresh "Ha" in intros r a Hr Ha; cbn [ss_mem In] in Hr;
  repeat (destruct Hr as [<-|Hr]; [cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val] in Ha; env_simp_in Ha; rewrite ?E2 in Ha; unfold O_ in *; lia|]); destruct Hr.
Lemma buf_side : forall data cap lo hi, 0 < cap -> lo < hi -> (forall i, 0 <= i < cap -> data + i < lo \/ hi <= data + i) ->
  data + cap <= lo \/ hi <= data.
Proof.
intros data cap lo hi Hc Hlh HB. destruct (ext_apart lo hi data cap data cap Hc ltac:(lia) ltac:(lia) ltac:(lia) HB) as [X|[X|X]]; lia.
Qed.

Lemma grant_wvb : forall md l mat a n, YK13.grant_ok_na_pin (with_vm_backing l mat md) a n = YK13.grant_ok_na_pin md a n.
Proof. intros. reflexivity. Qed.
Lemma vm_frameH : forall (H H' : word -> bool) (mem mem' : word -> option byte) a n v,
  (forall k, (k < n)%nat -> H' (Z_to_bv 64 (a + Z.of_nat k)) = H (Z_to_bv 64 (a + Z.of_nat k)) /\
     mem' (Z_to_bv 64 (a + Z.of_nat k)) = mem (Z_to_bv 64 (a + Z.of_nat k))) ->
  val_mem tfibsegs (mrestrict H mem) a n v -> val_mem tfibsegs (mrestrict H' mem') a n v.
Proof.
intros H H' mem mem' a n v F V k Hk. rewrite <- (V k Hk). destruct (F k Hk) as [F1 F2].
unfold mbyte, mrestrict. rewrite F1, F2. reflexivity.
Qed.
Lemma mbyte_H : forall (H H' : word -> bool) (mem mem' : word -> option byte) a,
  H' (Z_to_bv 64 a) = H (Z_to_bv 64 a) -> mem' (Z_to_bv 64 a) = mem (Z_to_bv 64 a) ->
  mbyte tfibsegs (mrestrict H' mem') a = mbyte tfibsegs (mrestrict H mem) a.
Proof. intros H H' mem mem' a E1 E2. unfold mbyte, mrestrict. rewrite E1, E2. reflexivity. Qed.
Lemma st_ok_havoc_ext : forall k E ss ms ws, st_ok tfibsegs E ss ms -> ss_atoms_lt k ss = true -> st_ok tfibsegs (havoc E k ws) ss ms.
Proof. intros k E ss ms ws HS Hk. eapply st_ok_agree; [exact HS | | exact Hk]. apply (env_agree_havoc_ge k k E E ws ltac:(lia) (env_agree_refl k E)). Qed.

Lemma same_io_wvb2 : forall (a b : Model) l1 m1 l2 m2, same_io (with_vm_backing l1 m1 a) (with_vm_backing l2 m2 b) -> same_io a b.
Proof. intros a b l1 m1 l2 m2 H. destruct a, b. unfold same_io, with_vm_backing in *. cbn in *. exact H. Qed.
Lemma same_io_wvb3 : forall (a b : Model) l m, same_io a b -> same_io a (with_vm_backing l m b).
Proof. intros a b l m H. destruct b. unfold same_io, with_vm_backing in *. cbn in *. exact H. Qed.

(* ---------------------------------------------------------------------------------------------------------------- *)
(* 4. Case: the buffer is mapped and has room (no Realloc).                                                          *)
Definition keep_post (W : world tfibsegs) (regs : bvmap 5 word) (mem : word -> option byte) (md : Model)
  (data cap size : Z) (s : list Z) (W' : world tfibsegs) (c' : config) : Prop :=
  let sp := bv_unsigned (getr regs 2) in let len := Z.of_nat (length s) in
  W' = W /\ exists regs' mem' mat,
  c' = mkCfg (mkst regs' (getr regs 1) mem' (seg_rom tfibsegs)) (with_vm_backing (m_vm_lazy md) mat md) /\
  regs_preserved regs regs' /\
  (forall x : word, ~ (sp - 512 <= bv_unsigned x < sp) -> ~ (O_ <= bv_unsigned x < O_ + 56) ->
     ~ (data + size <= bv_unsigned x < data + size + len) -> mem' x = mem x) /\
  (forall a, apresent (w_H W) mem a -> apresent (w_H W) mem' a) /\
  val_mem tfibsegs (mrestrict (w_H W) mem') O_ 8 (O_ + 32) /\ val_mem tfibsegs (mrestrict (w_H W) mem') (O_ + 16) 8 0 /\
  val_mem tfibsegs (mrestrict (w_H W) mem') (O_ + 32) 8 data /\ val_mem tfibsegs (mrestrict (w_H W) mem') (O_ + 40) 8 cap /\
  val_mem tfibsegs (mrestrict (w_H W) mem') (O_ + 48) 8 (size + len) /\
  (forall i, (i < length s)%nat -> mem' (Z_to_bv 64 (data + size + Z.of_nat i)) = Some (Z_to_bv 8 (nth i s 0))).

Lemma app_keep : forall (W : world tfibsegs) (regs : bvmap 5 word) (mem : word -> option byte) (md : Model)
  (p data cap size : Z) (s : list Z),
  let H := w_H W in let m := mrestrict H mem in let sp := bv_unsigned (getr regs 2) in let len := Z.of_nat (length s) in
  sp mod 16 = 0 -> TFIB_IMG_END + 512 <= sp -> (forall a, sp - 512 <= a < sp -> apresent H mem a) ->
  val_mem tfibsegs m O_ 8 (O_ + 32) -> val_mem tfibsegs m (O_ + 16) 8 0 -> val_mem tfibsegs m (O_ + 32) 8 data ->
  val_mem tfibsegs m (O_ + 40) 8 cap -> val_mem tfibsegs m (O_ + 48) 8 size ->
  val_mem tfibsegs m 0x103a0 8 0xafffff00000fffff ->
  getr regs 10 = Z_to_bv 64 p -> sp <= p -> p + len + 1 < 2 ^ 64 -> YK0s.ret_ok (getr regs 1) ->
  (forall i, (i < length s)%nat -> val_mem tfibsegs m (p + Z.of_nat i) 1 (nth i s 0) /\ 0 < nth i s 0 < 256) ->
  val_mem tfibsegs m (p + len) 1 0 ->
  0 <= size -> size + len <= cap -> cap < 2 ^ 47 -> 0 < cap -> 0 <= data -> data + cap < 2 ^ 64 ->
  (forall i, 0 <= i < cap -> apresent H mem (data + i) /\ (data + i < TFIB_IMG_LO \/ TFIB_IMG_END <= data + i) /\
     (data + i < sp - 512 \/ p + len + 1 <= data + i)) ->
  SRr tfibsegs W (mkCfg (mkst regs (Z_to_bv 64 0x56418) mem (seg_rom tfibsegs)) md) (keep_post W regs mem md data cap size s).
Proof.
intros W regs mem md p data cap size s. cbv zeta.
intros Hal Hsp HPRES V0 V16 V32 V40 V48 VK H10 Hp Hp64 Hra HSTR HNUL Hs0 Hkeep Hcap Hcap0 Hd0 Hdc HB.
pose proof Hwx_tfa as Hwx. pose proof (u64_range (getr regs 2)) as Usp.
set (len := Z.of_nat (length s)) in *.
assert (Hlen0 : 0 <= len) by lia.
pose proof (seed_ok W regs mem (O_ + 32) data cap size Hal Hsp ltac:(intros a Ha; apply HPRES; lia)
  ltac:(unfold O_; lia) ltac:(lia) ltac:(lia) ltac:(lia) V0 V16 V32 V40 V48 VK) as HS.
assert (E2 : ew (Eseed regs data cap size) 2 = getr regs 2) by (exact (ew_seed_reg regs _ _ _ 2 2%bv eq_refl)).
set (sp := bv_unsigned (getr regs 2)) in *.
unfold TFIB_IMG_END, TFIB_IMG_LO in *.
destruct (str_bytes _ p s HSTR HNUL) as [HNZ HRD]. rewrite length_map in HRD.
set (d := data + size).
(* every zone the walk writes *)
assert (SB1 : data + cap <= sp - 512 \/ p + len + 1 <= data)
  by (apply (buf_side data cap); [lia | lia | intros i Hi; destruct (HB i Hi) as (_ & _ & X); exact X]).
assert (SB2 : data + cap <= 0x10000 \/ 0x5fc000 <= data)
  by (apply (buf_side data cap); [lia | lia | intros i Hi; destruct (HB i Hi) as (_ & X & _); exact X]).
(* --- entry to internal_strlen --- *)
srun_to HS 0x653b0. intros ms1 mat1 HS HF HG. after_run HS HF HG.
fkeep HF E2 KW1. rewrite E2 in KW1. fold sp in KW1.
assert (PR1 : forall a, apresent (w_H W) mem a -> apresent (w_H W) (ms_mem ms1) a) by (intros a; apply apresent_grows; exact HG). clear HG.
regv HS (10%bv : bv 5) p Q10 ltac:(rewrite (ew_seed_reg regs _ _ _ 10 10%bv eq_refl), H10; rewrite unsigned_lit_small by lia; unfold zcanon, M64; rewrite Z.add_0_r, Z.mod_small by lia; reflexivity).
rreg HS (1%bv : bv 5) Q1.
eapply (istrlen_stretch_gen W 35 _ _ _ _ p 0x56558 (map (Z_to_bv 8) s));
[ exact HS | reflexivity | reflexivity | vm_compute; reflexivity | vm_compute; reflexivity | exact Q10 | exact Q1
| lia | rewrite length_map; lia | exact HNZ | | reflexivity | lia | clear HS Q10 Q1 ].
{ intros j Hj. rewrite length_map in Hj. rewrite (mbyte_mrestrict_same (w_H W) mem (ms_mem ms1)); [apply HRD; exact Hj|]. apply KW1.
  rewrite unsigned_lit_small by lia. unfold AZ, O_. lia. }
intros regs2 mat2 HS R10 _. rewrite wvb_collapse. rewrite length_map in R10. fold len in R10.
assert (A35 : ew (havoc (Eseed regs data cap size) 35 (map (getr regs2) [10%bv; 11%bv; 12%bv])) 35 = Z_to_bv 64 len)
  by (rewrite <- R10; exact (ew_havoc_new (Eseed regs data cap size) 35 (map (getr regs2) [10%bv; 11%bv; 12%bv]) 0 (Z_to_bv 64 0) ltac:(apply Nat.ltb_lt; reflexivity))).
(* --- the room test at 0x56568: size >= size + len --- *)
srun HS. intros ms3 mat3 HS HF HG. after_run HS HF HG.
fkeep HF E2 KW3. env_simp_in KW3. rewrite E2 in KW3. fold sp in KW3.
assert (PR3 : forall a, apresent (w_H W) mem a -> apresent (w_H W) (ms_mem ms3) a) by (intros a Ha; apply (apresent_grows _ _ _ _ HG), PR1, Ha). clear HG PR1.
assert (EQ3 : forall x : word, ~ AZ sp (bv_unsigned x) -> ~ (d <= bv_unsigned x < d + len) -> ms_mem ms3 x = mem x)
  by (intros x Hx _; rewrite KW3 by exact Hx; apply KW1, Hx). clear KW1 KW3.
srr_branch_sh tbl_app_ok HS.
- (* size >= size + len: len = 0, straight to the copy *)
  brnorm Hc A35. apply negb_true_iff, Z.ltb_ge in Hc. assert (L0 : len = 0) by lia.
  srun_to HS 0x651e0. intros ms4 mat4 HS HF HG. after_run HS HF HG.
  step_frame E2 EQ3 PR3 EQm PRm HF HG.
  regv HS (10%bv : bv 5) d Q10 ltac:(subst d; zfin A35).
  regv HS (11%bv : bv 5) p Q11 ltac:(rewrite (ew_seed_reg regs _ _ _ 10 10%bv eq_refl), H10; zfin A35).
  regv HS (12%bv : bv 5) len Q12 ltac:(zfin A35).
  rreg HS (1%bv : bv 5) Q1.
  eapply (imemcpy_stretch_gen W 38%nat _ _ _ _ d p len 0x565b4 (map (Z_to_bv 8) s));
  [ exact HS | reflexivity | reflexivity | vm_compute; reflexivity | vm_compute; reflexivity
  | exact Q10 | exact Q11 | exact Q12 | exact Q1 | rewrite length_map; reflexivity
  | lia | lia | lia | lia | lia | | | reflexivity | lia | hext E2 | hext64 E2 | clear HS Q10 Q11 Q12 Q1 ].
  { intros a Ha; apply PRm; destruct (HB (a - data) ltac:(subst d; lia)) as (X & _ & _).
    replace (data + (a - data)) with a in X by lia; exact X. }
  { intros j Hj; rewrite length_map in Hj.
    rewrite (mbyte_mrestrict_same (w_H W) mem (ms_mem ms4)) by (apply EQm; rewrite unsigned_lit_small by lia; unfold AZ, O_; lia).
    rewrite (HRD j ltac:(lia)), app_nth1 by (rewrite length_map; exact Hj); reflexivity. }
  intros regs8 mem8 mat8 HS _ _ Hout8 Hpres8 Hcopy8. rewrite wvb_collapse.
  assert (EQc : forall x : word, ~ AZ sp (bv_unsigned x) -> ~ (d <= bv_unsigned x < d + len) -> mem8 x = mem x)
    by (intros x H1 H2; rewrite (Hout8 x H2); exact (EQm x H1 H2)).
  assert (PRc : forall a, apresent (w_H W) mem a -> apresent (w_H W) mem8 a) by (intros a Ha; apply Hpres8, PRm, Ha).
  clear EQm PRm Hout8 Hpres8.
  srun_to HS 0x5669c. intros msR matR HS HF HG. after_run HS HF HG.
  fkeep HF E2 KWR. env_simp_in KWR. rewrite E2 in KWR.
  eapply (SRr_ret_at tfibsegs tbl_app tbl_app_ok Hwx W _ _ msR _ _ HS); [reflexivity | vm_compute; reflexivity |].
  intros mat'. rewrite ?wvb_collapse.
  unfold keep_post; cbv zeta; split; [reflexivity|].
  exists (ms_regs msR), (ms_mem msR), mat'.
  rreg HS (1%bv : bv 5) QR1. env_simp_in QR1. rewrite (ew_seed_reg regs _ _ _ 1 1%bv eq_refl) in QR1.
  split; [rewrite QR1; unfold YK0s.ret_ok in Hra; rewrite Hra; reflexivity|].
  split; [apply (regs_preserved_of_st_ok tfibsegs _ _ _ regs [Z_to_bv 64 data; Z_to_bv 64 cap; Z_to_bv 64 size] HS);
          [repeat (apply env_agree_havoc_ge; [lia|]); unfold Eseed; apply env_agree_refl | vm_compute; reflexivity]|].
  split; [intros x H1 H2 H3; rewrite KWR by (unfold AZ; lia); exact (EQc x ltac:(unfold AZ; lia) H3)|].
  split; [intros a Ha; apply (apresent_grows _ _ _ _ HG), PRc, Ha|].
  split; [memv HS 1%nat 1%nat; [unfold O_; lia | reflexivity | unfold O_; lia]|].
  split; [memv HS 1%nat 0%nat; [unfold O_; lia | reflexivity | lia]|].
  split; [memv HS 2%nat 0%nat; [unfold O_; lia | cbn [sv_denot]; env_simp; rewrite ew_seed32, unsigned_lit_small, Z.add_0_r by lia; reflexivity | lia]|].
  split; [memv HS 2%nat 1%nat; [unfold O_; lia | cbn [sv_denot]; env_simp; rewrite ew_seed33, unsigned_lit_small, Z.add_0_r by lia; reflexivity | lia]|].
  split; [memv HS 3%nat 0%nat; [unfold O_; lia |
    apply bv_eq; rewrite unsigned_lit_small by lia;
    match goal with |- bv_unsigned (sv_denot ?E ?e) = _ => change (bv_unsigned (sv_denot E e)) with (U E e) end;
    rewrite U_zev by reflexivity; cbn [zev zalu_raw]; unfold rho_of; env_simp; zfin A35 | lia]|].
  intros i Hi. rewrite KWR by (rewrite unsigned_lit_small by lia; unfold AZ, O_; lia).
  pose proof (Hcopy8 i ltac:(rewrite length_map; exact Hi)) as C. rewrite (map_nth (Z_to_bv 8) s 0 i) in C. exact C.
- brnorm Hc A35. apply negb_false_iff, Z.ltb_lt in Hc.
  srun HS. intros ms4 mat4 HS HF HG. after_run HS HF HG.
  step_frame E2 EQ3 PR3 EQ4 PR4 HF HG.
  srr_branch_sh tbl_app_ok HS.
  + brnorm Hc0 A35. apply negb_true_iff, Z.ltb_ge in Hc0.
    srun_to HS 0x6525c. intros ms5 mat5 HS HF HG. after_run HS HF HG.
    step_frame E2 EQ4 PR4 EQ5 PR5 HF HG.
    regv HS (10%bv : bv 5) d Q10 ltac:(subst d; zfin A35).
    regv HS (11%bv : bv 5) 0 Q11 ltac:(zfin A35).
    regv HS (12%bv : bv 5) len Q12 ltac:(zfin A35).
    rreg HS (1%bv : bv 5) Q1.
    eapply (imemset_stretch_gen W 38 _ _ _ _ d len 0x56598);
    [ exact HS | reflexivity | reflexivity | vm_compute; reflexivity | vm_compute; reflexivity
    | exact Q10 | exact Q11 | exact Q12 | exact Q1 | lia | lia | lia | | reflexivity | lia | hext E2 | hext64 E2
    | clear HS Q10 Q11 Q12 Q1 ].
    { intros a Ha. apply PR5. destruct (HB (a - data) ltac:(subst d; lia)) as (X & _ & _). replace (data + (a - data)) with a in X by lia. exact X. }
    intros regs6 mem6 mat6 HS _ _ Hout6 Hpres6 _. rewrite wvb_collapse.
    assert (EQm : forall x : word, ~ AZ sp (bv_unsigned x) -> ~ (d <= bv_unsigned x < d + len) -> mem6 x = mem x)
      by (intros x H1 H2; rewrite (Hout6 x H2); exact (EQ5 x H1 H2)).
    assert (PRm : forall a, apresent (w_H W) mem a -> apresent (w_H W) mem6 a) by (intros a Ha; apply Hpres6, PR5, Ha).
    clear EQ5 PR5 Hout6 Hpres6.
    srun_to HS 0x651e0. intros ms7 mat7 HS HF HG. after_run HS HF HG.
    step_frame E2 EQm PRm EQ7 PR7 HF HG.
    regv HS (10%bv : bv 5) d Q10 ltac:(subst d; zfin A35).
    regv HS (11%bv : bv 5) p Q11 ltac:(rewrite (ew_seed_reg regs _ _ _ 10 10%bv eq_refl), H10; zfin A35).
    regv HS (12%bv : bv 5) len Q12 ltac:(zfin A35).
    rreg HS (1%bv : bv 5) Q1.
    eapply (imemcpy_stretch_gen W 41%nat _ _ _ _ d p len 0x565b4 (map (Z_to_bv 8) s));
    [ exact HS | reflexivity | reflexivity | vm_compute; reflexivity | vm_compute; reflexivity
    | exact Q10 | exact Q11 | exact Q12 | exact Q1 | rewrite length_map; reflexivity
    | lia | lia | lia | lia | lia | | | reflexivity | lia | hext E2 | hext64 E2 | clear HS Q10 Q11 Q12 Q1 ].
    { intros a Ha; apply PR7; destruct (HB (a - data) ltac:(subst d; lia)) as (X & _ & _).
      replace (data + (a - data)) with a in X by lia; exact X. }
    { intros j Hj; rewrite length_map in Hj.
      rewrite (mbyte_mrestrict_same (w_H W) mem (ms_mem ms7)) by (apply EQ7; rewrite unsigned_lit_small by lia; unfold AZ, O_; lia).
      rewrite (HRD j ltac:(lia)), app_nth1 by (rewrite length_map; exact Hj); reflexivity. }
    intros regs8 mem8 mat8 HS _ _ Hout8 Hpres8 Hcopy8. rewrite wvb_collapse.
    assert (EQc : forall x : word, ~ AZ sp (bv_unsigned x) -> ~ (d <= bv_unsigned x < d + len) -> mem8 x = mem x)
      by (intros x H1 H2; rewrite (Hout8 x H2); exact (EQ7 x H1 H2)).
    assert (PRc : forall a, apresent (w_H W) mem a -> apresent (w_H W) mem8 a) by (intros a Ha; apply Hpres8, PR7, Ha).
    clear EQ7 PR7 Hout8 Hpres8.
    srun_to HS 0x5669c. intros msR matR HS HF HG. after_run HS HF HG.
    fkeep HF E2 KWR. env_simp_in KWR. rewrite E2 in KWR.
    eapply (SRr_ret_at tfibsegs tbl_app tbl_app_ok Hwx W _ _ msR _ _ HS); [reflexivity | vm_compute; reflexivity |].
    intros mat'. rewrite ?wvb_collapse.
    unfold keep_post; cbv zeta; split; [reflexivity|].
    exists (ms_regs msR), (ms_mem msR), mat'.
    rreg HS (1%bv : bv 5) QR1. env_simp_in QR1. rewrite (ew_seed_reg regs _ _ _ 1 1%bv eq_refl) in QR1.
    split; [rewrite QR1; unfold YK0s.ret_ok in Hra; rewrite Hra; reflexivity|].
    split; [apply (regs_preserved_of_st_ok tfibsegs _ _ _ regs [Z_to_bv 64 data; Z_to_bv 64 cap; Z_to_bv 64 size] HS);
            [repeat (apply env_agree_havoc_ge; [lia|]); unfold Eseed; apply env_agree_refl | vm_compute; reflexivity]|].
    split; [intros x H1 H2 H3; rewrite KWR by (unfold AZ; lia); exact (EQc x ltac:(unfold AZ; lia) H3)|].
    split; [intros a Ha; apply (apresent_grows _ _ _ _ HG), PRc, Ha|].
    split; [memv HS 1%nat 1%nat; [unfold O_; lia | reflexivity | unfold O_; lia]|].
    split; [memv HS 1%nat 0%nat; [unfold O_; lia | reflexivity | lia]|].
    split; [memv HS 2%nat 0%nat; [unfold O_; lia | cbn [sv_denot]; env_simp; rewrite ew_seed32, unsigned_lit_small, Z.add_0_r by lia; reflexivity | lia]|].
    split; [memv HS 2%nat 1%nat; [unfold O_; lia | cbn [sv_denot]; env_simp; rewrite ew_seed33, unsigned_lit_small, Z.add_0_r by lia; reflexivity | lia]|].
    split; [memv HS 3%nat 0%nat; [unfold O_; lia |
      apply bv_eq; rewrite unsigned_lit_small by lia;
      match goal with |- bv_unsigned (sv_denot ?E ?e) = _ => change (bv_unsigned (sv_denot E e)) with (U E e) end;
      rewrite U_zev by reflexivity; cbn [zev zalu_raw]; unfold rho_of; env_simp; zfin A35 | lia]|].
    intros i Hi. rewrite KWR by (rewrite unsigned_lit_small by lia; unfold AZ, O_; lia).
    pose proof (Hcopy8 i ltac:(rewrite length_map; exact Hi)) as C. rewrite (map_nth (Z_to_bv 8) s 0 i) in C. exact C.
  + brnorm Hc0 A35. apply negb_false_iff, Z.ltb_lt in Hc0. lia.
Qed.

(* The post of a call that remapped the buffer once (cases 4 and, with data = cap = 0, the first map of 1 / 2).
   The world, grant and model facts are realloc_post_r's (RepAppRcf.v). *)
Definition remap_post (W : world tfibsegs) (regs : bvmap 5 word) (mem : word -> option byte) (md : Model)
  (data cap size : Z) (s : list Z) (W' : world tfibsegs) (c' : config) : Prop :=
  let sp := bv_unsigned (getr regs 2) in let len := Z.of_nat (length s) in let ncap := page_round_up_Z (size + len) in
  exists (a : Z) (mat matF : list word) (regs' : bvmap 5 word) (mem' : word -> option byte),
  let mdN := with_vm_backing (m_vm_lazy md) mat md in
  let md1 := Mmap.with_mmap_backing (w64 34) (w64 a) (w64 ncap) (YK0v.mmap_model (w64 a) (w64 ncap) mdN) in
  let mdU := if cap =? 0 then md1 else YK0v.munmap_model (w64 data) (w64 cap) md1 in
  let mdF := with_vm_backing (m_vm_lazy mdU) matF mdU in
  wle W W' /\ w_A W' = w_A W /\
  (forall x : word, a <= bv_unsigned x < a + ncap -> w_H W' x = false) /\
  (forall x : word, ~ (a <= bv_unsigned x < a + ncap) -> w_H W' x = w_H W x) /\
  YK13.grant_ok_na_pin md (w64 a) ncap = true /\ 0 < a /\ a + ncap < 2 ^ 64 /\
  c' = mkCfg (mkst regs' (getr regs 1) mem' (seg_rom tfibsegs)) mdF /\
  regs_preserved regs regs' /\
  (forall x : word, ~ (sp - 512 <= bv_unsigned x < sp) -> ~ (O_ <= bv_unsigned x < O_ + 56) ->
     ~ (a <= bv_unsigned x < a + ncap) -> ~ (data <= bv_unsigned x < data + cap) -> mem' x = mem x) /\
  (forall x : word, data <= bv_unsigned x < data + cap -> mem' x = None) /\
  (forall b, 0 <= b < 2 ^ 64 -> apresent (w_H W) mem b -> ~ (data <= b < data + cap) -> ~ (O_ <= b < O_ + 56) ->
     apresent (w_H W') mem' b) /\
  (forall b, a <= b < a + ncap -> apresent (w_H W') mem' b) /\
  val_mem tfibsegs (mrestrict (w_H W') mem') O_ 8 (O_ + 32) /\ val_mem tfibsegs (mrestrict (w_H W') mem') (O_ + 16) 8 0 /\
  val_mem tfibsegs (mrestrict (w_H W') mem') (O_ + 32) 8 a /\ val_mem tfibsegs (mrestrict (w_H W') mem') (O_ + 40) 8 ncap /\
  val_mem tfibsegs (mrestrict (w_H W') mem') (O_ + 48) 8 (size + len) /\
  same_io md mdF /\ amwf mdF.

(* ---------------------------------------------------------------------------------------------------------------- *)
(* 5. Case: the buffer is mapped and too small (one Realloc).                                                        *)
Section r.

Lemma app_grow : forall {R : Type} (K : Z -> itree astate R) (Q : R -> world tfibsegs -> config -> Prop) (snap : astate) (rq : Z)
  (W : world tfibsegs) (regs : bvmap 5 word) (mem : word -> option byte) (md : Model)
  (p data cap size : Z) (s : list Z),
  let H := w_H W in let m := mrestrict H mem in let sp := bv_unsigned (getr regs 2) in let len := Z.of_nat (length s) in
  let ncap := page_round_up_Z (size + len) in
  sp mod 16 = 0 -> TFIB_IMG_END + 512 <= sp -> (forall a, sp - 512 <= a < sp -> apresent H mem a) ->
  val_mem tfibsegs m O_ 8 (O_ + 32) -> val_mem tfibsegs m (O_ + 16) 8 0 -> val_mem tfibsegs m (O_ + 32) 8 data ->
  val_mem tfibsegs m (O_ + 40) 8 cap -> val_mem tfibsegs m (O_ + 48) 8 size ->
  val_mem tfibsegs m 0x103a0 8 0xafffff00000fffff ->
  getr regs 10 = Z_to_bv 64 p -> sp <= p -> p + len + 1 < 2 ^ 64 -> YK0s.ret_ok (getr regs 1) ->
  (forall i, (i < length s)%nat -> val_mem tfibsegs m (p + Z.of_nat i) 1 (nth i s 0) /\ 0 < nth i s 0 < 256) ->
  val_mem tfibsegs m (p + len) 1 0 ->
  0 <= size -> size <= cap -> cap < size + len -> size + len < 2 ^ 47 -> 0 < cap -> 0 <= data -> data + cap < 2 ^ 64 ->
  (forall i, 0 <= i < cap -> apresent H mem (data + i) /\ (data + i < TFIB_IMG_LO \/ TFIB_IMG_END <= data + i) /\
     (data + i < sp - 512 \/ p + len + 1 <= data + i)) ->
  amwf md ->
  (forall mat, Z.of_nat (length mat) * page_size <= A_bytes (w_A W) ->
     Placement.mmap_grant_refusable (w64 34) (with_vm_backing (m_vm_lazy md) mat md) ncap = false) ->
  (forall a : word, YK13.grant_ok_na_pin md a ncap = true ->
     (bv_unsigned a + ncap <= TFIB_IMG_LO \/ TFIB_IMG_END <= bv_unsigned a) /\
     (bv_unsigned a + ncap <= sp - 512 \/ p + len + 1 <= bv_unsigned a)) ->
  (forall (a2 : Z) (pg : word), YK13.grant_ok_na_pin md (w64 a2) ncap = true -> a2 <= bv_unsigned pg ->
     bv_unsigned pg + page_size <= a2 + ncap -> page_in_ranges pg (m_vm_lazy md) = false) ->
  eager_used md + A_bytes (w_A W) + ncap <= vm_limit (m_vmmaps md) ->
  val_mem tfibsegs m 0x9df30 8 0x1360e0 -> val_mem tfibsegs m 0x1360e0 8 4096 ->
  val_mem tfibsegs m 0x9df40 8 0x138168 -> val_mem tfibsegs m 0x13826c 1 0 -> val_mem tfibsegs m 0x1381f8 8 0 ->
  data mod 4096 = 0 -> cap mod 4096 = 0 -> data + cap <= TASK_SIZE -> In (w64 data, w64 cap) (vm_maps (m_vmmaps md)) -> 0 < data ->
  (forall W' c', remap_post W regs mem md data cap size s W' c' -> amreal tfibsegs (K 1) W' c' Q) ->
  amreal tfibsegs (IAsk (KMmapSec rq) snap K) W (mkCfg (mkst regs (Z_to_bv 64 0x56418) mem (seg_rom tfibsegs)) md) Q.
Proof.
intros R K Q snap rq W regs mem md p data cap size s. cbv zeta.
intros Hal Hsp HPRES V0 V16 V32 V40 V48 VK H10 Hp Hp64 Hra HSTR HNUL Hs0 Hsc Hlt Hcap Hcap0 Hd0 Hdc HB Hamwf HNR HGA HGL HGB VC1 VC2 VC3 VC4 VC5 Hdal Hcal Hdts Hdin Hdpos HK.
apply (amreal_SRr_pre tfibsegs _ _ _ _ (fun W' c' => amreal tfibsegs (IAsk (KMmapSec rq) snap K) W' c' Q)); [|intros W' c' _ X; exact X].
pose proof Hwx_tfa as Hwx. pose proof (u64_range (getr regs 2)) as Usp.
set (len := Z.of_nat (length s)) in *.
assert (Hlen0 : 0 <= len) by lia.
pose proof (seed_ok W regs mem (O_ + 32) data cap size Hal Hsp ltac:(intros a Ha; apply HPRES; lia)
  ltac:(unfold O_; lia) ltac:(lia) ltac:(lia) ltac:(lia) V0 V16 V32 V40 V48 VK) as HS.
assert (E2 : ew (Eseed regs data cap size) 2 = getr regs 2) by (exact (ew_seed_reg regs _ _ _ 2 2%bv eq_refl)).
set (sp := bv_unsigned (getr regs 2)) in *.
unfold TFIB_IMG_END, TFIB_IMG_LO in *.
destruct (str_bytes _ p s HSTR HNUL) as [HNZ HRD]. rewrite length_map in HRD.
set (d := data + size).
(* every zone the walk writes *)
assert (SB1 : data + cap <= sp - 512 \/ p + len + 1 <= data)
  by (apply (buf_side data cap); [lia | lia | intros i Hi; destruct (HB i Hi) as (_ & _ & X); exact X]).
assert (SB2 : data + cap <= 0x10000 \/ 0x5fc000 <= data)
  by (apply (buf_side data cap); [lia | lia | intros i Hi; destruct (HB i Hi) as (_ & X & _); exact X]).
(* --- entry to internal_strlen --- *)
srun_to HS 0x653b0. intros ms1 mat1 HS HF HG. after_run HS HF HG.
fkeep HF E2 KW1. rewrite E2 in KW1. fold sp in KW1.
assert (PR1 : forall a, apresent (w_H W) mem a -> apresent (w_H W) (ms_mem ms1) a) by (intros a; apply apresent_grows; exact HG). clear HG.
regv HS (10%bv : bv 5) p Q10 ltac:(rewrite (ew_seed_reg regs _ _ _ 10 10%bv eq_refl), H10; rewrite unsigned_lit_small by lia; unfold zcanon, M64; rewrite Z.add_0_r, Z.mod_small by lia; reflexivity).
rreg HS (1%bv : bv 5) Q1.
eapply (istrlen_stretch_gen W 35 _ _ _ _ p 0x56558 (map (Z_to_bv 8) s));
[ exact HS | reflexivity | reflexivity | vm_compute; reflexivity | vm_compute; reflexivity | exact Q10 | exact Q1
| lia | rewrite length_map; lia | exact HNZ | | reflexivity | lia | clear HS Q10 Q1 ].
{ intros j Hj. rewrite length_map in Hj. rewrite (mbyte_mrestrict_same (w_H W) mem (ms_mem ms1)); [apply HRD; exact Hj|]. apply KW1.
  rewrite unsigned_lit_small by lia. unfold AZ, O_. lia. }
intros regs2 mat2 HS R10 _. rewrite wvb_collapse. rewrite length_map in R10. fold len in R10.
assert (A35 : ew (havoc (Eseed regs data cap size) 35 (map (getr regs2) [10%bv; 11%bv; 12%bv])) 35 = Z_to_bv 64 len)
  by (rewrite <- R10; exact (ew_havoc_new (Eseed regs data cap size) 35 (map (getr regs2) [10%bv; 11%bv; 12%bv]) 0 (Z_to_bv 64 0) ltac:(apply Nat.ltb_lt; reflexivity))).
(* --- the room test at 0x56568: size >= size + len --- *)
srun HS. intros ms3 mat3 HS HF HG. after_run HS HF HG.
fkeep HF E2 KW3. env_simp_in KW3. rewrite E2 in KW3. fold sp in KW3.
assert (PR3 : forall a, apresent (w_H W) mem a -> apresent (w_H W) (ms_mem ms3) a) by (intros a Ha; apply (apresent_grows _ _ _ _ HG), PR1, Ha). clear HG PR1.
assert (EQ3 : forall x : word, ~ AZ sp (bv_unsigned x) -> ~ (d <= bv_unsigned x < d) -> ms_mem ms3 x = mem x)
  by (intros x Hx _; rewrite KW3 by exact Hx; apply KW1, Hx). clear KW1 KW3.
srr_branch_sh tbl_app_ok HS.
- brnorm Hc A35. apply negb_true_iff, Z.ltb_ge in Hc. lia.
- brnorm Hc A35. apply negb_false_iff, Z.ltb_lt in Hc.
  srun HS. intros ms4 mat4 HS HF HG. after_run HS HF HG.
  step_frame E2 EQ3 PR3 EQ4 PR4 HF HG.
  srr_branch_sh tbl_app_ok HS.
  + brnorm Hc0 A35. apply negb_true_iff, Z.ltb_ge in Hc0. lia.
  + brnorm Hc0 A35. apply negb_false_iff, Z.ltb_lt in Hc0.
    srun_to HS 0x59e3c. intros ms5 mat5 HS HF HG. after_run HS HF HG.
    step_frame E2 EQ4 PR4 EQ5 PR5 HF HG.
    apply SRr_ret. cbv beta.
    assert (Hvm : forall (x : Z) k, (k < 8)%nat -> 0x9df30 <= x -> x + 8 <= O_ \/ O_ + 56 <= x -> x + 8 <= 0x5fc000 ->
      ms_mem ms5 (Z_to_bv 64 (x + Z.of_nat k)) = mem (Z_to_bv 64 (x + Z.of_nat k))).
    { intros x k Hk H1 H2 H3. apply EQ5; rewrite unsigned_lit_small by lia; unfold AZ, O_ in *; lia. }
    regv HS (10%bv : bv 5) (O_ + 32) Q10 ltac:(unfold O_; zfin A35).
    regv HS (11%bv : bv 5) (size + len) Q11 ltac:(zfin A35).
    regv HS (2%bv : bv 5) (sp - 96) Q2 ltac:(rewrite (ew_seed_reg regs _ _ _ 2 2%bv eq_refl); fold sp; zfin A35).
    rreg HS (1%bv : bv 5) Q1.
    lazymatch type of HS with st_ok _ _ ?ss _ =>
      let rs := eval vm_compute in (match ss_mem ss with r0 :: r1 :: _ :: r3 :: r4 :: _ => [r0; r1; r3; r4] | _ => [] end) in
      eapply (RepAppRcf.realloc_stretch K Q snap rq W 38 _ _ rs ms5 _ (O_ + 32) (size + len) data cap size 0x56580)
    end;
    [ exact HS | reflexivity | reflexivity | vm_compute; reflexivity | vm_compute; reflexivity | vm_compute; reflexivity
    | vm_compute; reflexivity
    | apply submem_keep; [apply subregion_refl|]; apply submem_keep; [apply subregion_refl|]; apply submem_drop;
      apply submem_keep; [apply subregion_refl|]; apply submem_keep; [apply subregion_refl|]; apply submem_nil
    | reflexivity | | | | clear HS ].
    { (* Realloc's premises at the call *)
      unfold RepReallocD.realloc_pre, RepReallocD.REALLOC_STK, RepReallocD.REALLOC_FRAME, RepMmapcf.MOD_STK, TFIB_IMG_LO, TFIB_IMG_END. cbv zeta. rewrite Q2, unsigned_lit_small by lia.
      split; [exact Q10|]. split; [exact Q11|]. split; [rewrite Q1; apply ret_ok_of_mod2; [reflexivity | lia]|].
      split; [apply (amwf_same md); [reflexivity | reflexivity | exact Hamwf]|].
      split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|]. split; [unfold O_; lia|]. split; [unfold O_; lia|].
      split; [reflexivity|].
      split; [memv HS 2%nat 0%nat; [unfold O_; lia | cbn [sv_denot]; env_simp; rewrite ew_seed32, unsigned_lit_small, Z.add_0_r by lia; reflexivity | lia]|].
      split; [memv HS 2%nat 1%nat; [unfold O_; lia | cbn [sv_denot]; env_simp; rewrite ew_seed33, unsigned_lit_small, Z.add_0_r by lia; reflexivity | lia]|].
      split; [memv HS 3%nat 0%nat; [unfold O_; lia | cbn [sv_denot]; env_simp; rewrite ew_seed34, unsigned_lit_small, Z.add_0_r by lia; reflexivity | lia]|].
      split; [intros x Hx; apply rw_writable; unfold O_ in *; lia|].
      split; [left; unfold O_; lia|]. split; [unfold O_; lia|]. split; [unfold O_; lia|].
      split; [lia|]. split; [exact Hdts|].
      split; [right; split; [lia|]; split; [lia|]; split; [exact Hdal|]; split; [exact Hcal|]; exact Hdin|].
      split; [intros i Hi; apply PR5; destruct (HB i ltac:(lia)) as (X & _ & _); exact X|].
      split; [lia|]. split; [unfold O_; lia|].
      split; [apply (vm_frameH (w_H W) (w_H W) mem (ms_mem ms5)); [intros k Hk; split; [reflexivity | apply Hvm; unfold O_; lia] | exact VC1]|].
      split; [apply (vm_frameH (w_H W) (w_H W) mem (ms_mem ms5)); [intros k Hk; split; [reflexivity | apply Hvm; unfold O_; lia] | exact VC2]|].
      split; [apply (vm_frameH (w_H W) (w_H W) mem (ms_mem ms5)); [intros k Hk; split; [reflexivity | apply Hvm; unfold O_; lia] | exact VC3]|].
      split; [apply (vm_frameH (w_H W) (w_H W) mem (ms_mem ms5)); [intros k Hk; split; [reflexivity | apply Hvm; unfold O_; cbn in Hk; lia] | exact VC4]|].
      split; [apply (vm_frameH (w_H W) (w_H W) mem (ms_mem ms5)); [intros k Hk; split; [reflexivity | apply Hvm; unfold O_; lia] | exact VC5]|].
      split; [intros mat Hm; rewrite wvb_collapse; exact (HNR mat Hm)|].
      split; [intros a Ha; rewrite grant_wvb in Ha; destruct (HGA a Ha) as [G1 G2]; split; [exact G1|]; split; [lia | unfold O_; lia]|].
      split; [intros a2 pg Ha2 Hpg1 Hpg2; rewrite grant_wvb in Ha2; exact (HGL a2 pg Ha2 Hpg1 Hpg2)|].
      split; [rewrite eager_used_wvb, m_vmmaps_wvb; exact HGB|].
      split; [replace (sp - 96) with (sp + (-6) * 16) by lia; rewrite Z_mod_plus_full; exact Hal|].
      split; [lia|].
      intros b Hb. apply PR5, HPRES. lia. }
    { intros r x Hr Hx. rewrite Q2, unsigned_lit_small by lia. unfold RepReallocD.REALLOC_STK, RepReallocD.REALLOC_FRAME, RepMmapcf.MOD_STK.
      cbn [In] in Hr; repeat (destruct Hr as [<-|Hr]; [cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val] in Hx; env_simp_in Hx; rewrite ?E2 in Hx; unfold O_ in *; lia|]); destruct Hr. }
    { intros r x Hr Hx a Ha. rewrite grant_wvb in Ha. destruct (HGA a Ha) as [G1 G2].
      cbn [In] in Hr; repeat (destruct Hr as [<-|Hr]; [cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val] in Hx; env_simp_in Hx; rewrite ?E2 in Hx; unfold O_ in *; lia|]); destruct Hr. }
    intros W' regs' mem' mdx HP HS.
    set (ncap := page_round_up_Z (size + len)) in *.
    pose proof (YK02.page_round_up_Z_bounds (size + len) ltac:(lia)) as NCB. fold ncap in NCB. unfold page_size in NCB.
    pose proof (YK10.page_round_up_Z_aligned (size + len)) as NCA. fold ncap in NCA. unfold page_size in NCA.
    unfold RepReallocD.realloc_post in HP. cbv zeta in HP. rewrite Q2, unsigned_lit_small in HP by lia.
    unfold RepReallocD.REALLOC_STK, RepReallocD.REALLOC_FRAME, RepMmapcf.MOD_STK in HP.
    destruct HP as (a & regsR & memR & matN & matM & Hwle & HwA & HwH1 & HwH2 & Hgr & Ha0 & Ha1 & Hc' & Hrp & VA & VC & VS &
      Hcp & Hz & Hold & FRr & PRr & NBr & Hio & Hmw).
    clear Q10 Q11 Q1 Q2.
    assert (Emem : mem' = memR) by (apply (f_equal (fun c => ms_mem (cfg_ms c))) in Hc'; exact Hc').
    assert (Emd : mdx = with_vm_backing (m_vm_lazy (if cap =? 0 then Mmap.with_mmap_backing (w64 34) (w64 a) (w64 ncap)
        (YK0v.mmap_model (w64 a) (w64 ncap) (with_vm_backing (m_vm_lazy (with_vm_backing (m_vm_lazy md) mat5 md)) matN (with_vm_backing (m_vm_lazy md) mat5 md))) else
        YK0v.munmap_model (w64 data) (w64 cap) (Mmap.with_mmap_backing (w64 34) (w64 a) (w64 ncap)
        (YK0v.mmap_model (w64 a) (w64 ncap) (with_vm_backing (m_vm_lazy (with_vm_backing (m_vm_lazy md) mat5 md)) matN (with_vm_backing (m_vm_lazy md) mat5 md)))))) matM
        (if cap =? 0 then Mmap.with_mmap_backing (w64 34) (w64 a) (w64 ncap)
        (YK0v.mmap_model (w64 a) (w64 ncap) (with_vm_backing (m_vm_lazy (with_vm_backing (m_vm_lazy md) mat5 md)) matN (with_vm_backing (m_vm_lazy md) mat5 md))) else
        YK0v.munmap_model (w64 data) (w64 cap) (Mmap.with_mmap_backing (w64 34) (w64 a) (w64 ncap)
        (YK0v.mmap_model (w64 a) (w64 ncap) (with_vm_backing (m_vm_lazy (with_vm_backing (m_vm_lazy md) mat5 md)) matN (with_vm_backing (m_vm_lazy md) mat5 md))))))
      by (apply (f_equal cfg_model) in Hc'; exact Hc').
    subst mem' mdx. rewrite !wvb_collapse in *. clear Hc'.
    rewrite grant_wvb in Hgr.
    assert (Ua : bv_unsigned (w64 a) = a) by (unfold w64; apply unsigned_lit_small; lia).
    destruct (HGA (w64 a) Hgr) as [GA1 GA2]. rewrite Ua in GA1, GA2.
    assert (GOD : a + ncap <= data \/ data + cap <= a).
    { pose proof (YGcfXs.grant_apart_cf md a ncap data cap Hgr ltac:(lia) ltac:(lia) Hdin ltac:(lia) ltac:(lia)) as Z1.
      unfold zdisjoint in Z1. cbn [fst snd] in Z1. lia. }
    (* the entry memory, outside the zones, through Realloc *)
    assert (EQR : forall x : word, ~ AZ sp (bv_unsigned x) -> ~ (a <= bv_unsigned x < a + ncap) -> ~ (data <= bv_unsigned x < data + cap) -> memR x = mem x).
    { intros x H1 H2 H3. rewrite FRr by (unfold AZ, O_ in *; lia). apply EQ5; [exact H1 | lia]. }
    assert (PRR : forall b, 0 <= b < 2 ^ 64 -> apresent (w_H W) mem b -> ~ (data <= b < data + cap) -> ~ (O_ <= b < O_ + 56) -> apresent (w_H W') memR b).
    { intros b Hb Hp1 Hn1 Hn2. apply PRr; [lia | apply PR5, Hp1 | exact Hn1 | unfold O_ in *; lia]. }
    clear FRr PRr EQ5 PR5 Hvm.
    (* the object's data / capacity words again, now as atoms 54 / 55 *)
    apply (st_ok_havoc_ext 54 _ _ _ [Z_to_bv 64 a; Z_to_bv 64 ncap]) in HS; [| vm_compute; reflexivity].
    assert (A54 : forall E, ew (havoc E 54 [Z_to_bv 64 a; Z_to_bv 64 ncap]) 54 = Z_to_bv 64 a)
      by (intros E; exact (ew_havoc_new E 54 [Z_to_bv 64 a; Z_to_bv 64 ncap] 0 (Z_to_bv 64 0) ltac:(apply Nat.ltb_lt; reflexivity))).
    assert (A55 : forall E, ew (havoc E 54 [Z_to_bv 64 a; Z_to_bv 64 ncap]) 55 = Z_to_bv 64 ncap)
      by (intros E; exact (ew_havoc_new E 54 [Z_to_bv 64 a; Z_to_bv 64 ncap] 1 (Z_to_bv 64 0) ltac:(apply Nat.ltb_lt; reflexivity))).
    apply (st_ok_add_region _ _ _ (YP09.mkRegion None (O_ + 32) (O_ + 48) (O_ + 32) (O_ + 48)
      [YP09.mkChunk (O_ + 32) (CVal 8 (SOff 54 0)); YP09.mkChunk (O_ + 40) (CVal 8 (SOff 55 0))])) in HS;
    [ | reflexivity
    | unfold region_ok; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val ms_mem restrict mkst];
      unfold O_; split; [lia|]; split; [lia|]; split; [intros o Ho; apply rw_writable; lia|];
      apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]];
      [ apply (chunk_ok_val tfibsegs _ _ _ _ _ _ a); [cbn [sv_denot]; rewrite A54, unsigned_lit_small, Z.add_0_r by lia; reflexivity | cbn; lia | cbn; lia | rewrite Z.add_0_l; exact VA]
      | apply (chunk_ok_val tfibsegs _ _ _ _ _ _ ncap); [cbn [sv_denot]; rewrite A55, unsigned_lit_small, Z.add_0_r by lia; reflexivity | cbn; lia | cbn; lia | rewrite Z.add_0_l; exact VC] ]
    | cbn [all_disjoint ss_mem ss_after_call]; unfold extent_disjoint; cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val]; env_simp; rewrite E2; unfold O_; repeat split; lia ].
    cbn [ss_pc ss_regs ss_mem ss_resv ss_facts] in HS.
    assert (OB1 : data + cap <= sp - 512 \/ p + len + 1 <= data) by exact SB1.
    apply (amreal_SRr_pre tfibsegs _ _ _ _ (fun W2 c2 => amreal tfibsegs (K 1) W2 c2 Q)); [|intros W2 c2 _ X; exact X].
    (* --- to internal_memset over the new buffer --- *)
    srun_to HS 0x6525c. intros ms6 mat6 HS HF HG. after_run HS HF HG.
    fkeep HF E2 KW6. env_simp_in KW6. rewrite E2 in KW6.
    assert (EQ6 : forall x : word, ~ AZ sp (bv_unsigned x) -> ~ (a <= bv_unsigned x < a + ncap) -> ~ (data <= bv_unsigned x < data + cap) -> ms_mem ms6 x = mem x)
      by (intros x H1 H2 H3; rewrite (KW6 x H1); exact (EQR x H1 H2 H3)).
    assert (OLD6 : forall x : word, data <= bv_unsigned x < data + cap -> ms_mem ms6 x = None)
      by (intros x Hx; rewrite KW6 by (unfold AZ, O_; lia); exact (Hold x Hx)).
    assert (PR6 : forall b, 0 <= b < 2 ^ 64 -> apresent (w_H W) mem b -> ~ (data <= b < data + cap) -> ~ (O_ <= b < O_ + 56) -> apresent (w_H W') (ms_mem ms6) b)
      by (intros b Hb H1 H2 H3; apply (apresent_grows _ _ _ _ HG), PRR; assumption).
    assert (NB6 : forall b, a <= b < a + ncap -> apresent (w_H W') (ms_mem ms6) b) by (intros b Hb; apply (apresent_grows _ _ _ _ HG), NBr, Hb).
    clear KW6 HG EQR Hold PRR NBr.
    regv HS (10%bv : bv 5) (a + size) Q10 ltac:(rewrite ?A54, ?A55; zfin A35).
    regv HS (11%bv : bv 5) 0 Q11 ltac:(zfin A35).
    regv HS (12%bv : bv 5) len Q12 ltac:(zfin A35).
    rreg HS (1%bv : bv 5) Q1.
    eapply (imemset_stretch_gen W' 56 _ _ _ _ (a + size) len 0x56598);
    [ exact HS | reflexivity | reflexivity | vm_compute; reflexivity | vm_compute; reflexivity
    | exact Q10 | exact Q11 | exact Q12 | exact Q1 | lia | lia | lia | | reflexivity | lia | hext E2 | hext64 E2
    | clear HS Q10 Q11 Q12 Q1 ].
    { intros b Hb. apply NB6. lia. }
    intros regs7 mem7 mat7 HS _ _ Hout7 Hpres7 _. rewrite wvb_collapse.
    assert (EQ7 : forall x : word, ~ AZ sp (bv_unsigned x) -> ~ (a <= bv_unsigned x < a + ncap) -> ~ (data <= bv_unsigned x < data + cap) -> mem7 x = mem x)
      by (intros x H1 H2 H3; rewrite Hout7 by lia; exact (EQ6 x H1 H2 H3)).
    assert (OLD7 : forall x : word, data <= bv_unsigned x < data + cap -> mem7 x = None)
      by (intros x Hx; rewrite Hout7 by lia; exact (OLD6 x Hx)).
    assert (PR7 : forall b, 0 <= b < 2 ^ 64 -> apresent (w_H W) mem b -> ~ (data <= b < data + cap) -> ~ (O_ <= b < O_ + 56) -> apresent (w_H W') mem7 b)
      by (intros b Hb H1 H2 H3; apply Hpres7, PR6; assumption).
    assert (NB7 : forall b, a <= b < a + ncap -> apresent (w_H W') mem7 b) by (intros b Hb; apply Hpres7, NB6, Hb).
    clear Hout7 Hpres7 EQ6 OLD6 PR6 NB6.
    (* --- to internal_memcpy --- *)
    srun_to HS 0x651e0. intros ms8 mat8 HS HF HG. after_run HS HF HG.
    fkeep HF E2 KW8. env_simp_in KW8. rewrite E2 in KW8.
    assert (EQ8 : forall x : word, ~ AZ sp (bv_unsigned x) -> ~ (a <= bv_unsigned x < a + ncap) -> ~ (data <= bv_unsigned x < data + cap) -> ms_mem ms8 x = mem x)
      by (intros x H1 H2 H3; rewrite (KW8 x H1); exact (EQ7 x H1 H2 H3)).
    assert (OLD8 : forall x : word, data <= bv_unsigned x < data + cap -> ms_mem ms8 x = None)
      by (intros x Hx; rewrite KW8 by (unfold AZ, O_; lia); exact (OLD7 x Hx)).
    assert (PR8 : forall b, 0 <= b < 2 ^ 64 -> apresent (w_H W) mem b -> ~ (data <= b < data + cap) -> ~ (O_ <= b < O_ + 56) -> apresent (w_H W') (ms_mem ms8) b)
      by (intros b Hb H1 H2 H3; apply (apresent_grows _ _ _ _ HG), PR7; assumption).
    assert (NB8 : forall b, a <= b < a + ncap -> apresent (w_H W') (ms_mem ms8) b) by (intros b Hb; apply (apresent_grows _ _ _ _ HG), NB7, Hb).
    clear KW8 HG EQ7 OLD7 PR7 NB7.
    regv HS (10%bv : bv 5) (a + size) Q10 ltac:(rewrite ?A54, ?A55; zfin A35).
    regv HS (11%bv : bv 5) p Q11 ltac:(rewrite (ew_seed_reg regs _ _ _ 10 10%bv eq_refl), H10; zfin A35).
    regv HS (12%bv : bv 5) len Q12 ltac:(zfin A35).
    rreg HS (1%bv : bv 5) Q1.
    eapply (imemcpy_stretch_gen W' 59 _ _ _ _ (a + size) p len 0x565b4 (map (Z_to_bv 8) s));
    [ exact HS | reflexivity | reflexivity | vm_compute; reflexivity | vm_compute; reflexivity
    | exact Q10 | exact Q11 | exact Q12 | exact Q1 | rewrite length_map; reflexivity
    | lia | lia | lia | lia | lia | | | reflexivity | lia | hext E2 | hext64 E2 | clear HS Q10 Q11 Q12 Q1 ].
    { intros b Hb. apply NB8. lia. }
    { intros j Hj. rewrite length_map in Hj.
      rewrite (mbyte_H (w_H W) (w_H W') mem (ms_mem ms8)); [rewrite (HRD j ltac:(lia)), app_nth1 by (rewrite length_map; exact Hj); reflexivity | |].
      - apply HwH2. rewrite unsigned_lit_small by lia. lia.
      - apply EQ8; rewrite unsigned_lit_small by lia; unfold AZ, O_; lia. }
    intros regs9 mem9 mat9 HS _ _ Hout9 Hpres9 _. rewrite wvb_collapse.
    assert (EQ9 : forall x : word, ~ AZ sp (bv_unsigned x) -> ~ (a <= bv_unsigned x < a + ncap) -> ~ (data <= bv_unsigned x < data + cap) -> mem9 x = mem x)
      by (intros x H1 H2 H3; rewrite Hout9 by lia; exact (EQ8 x H1 H2 H3)).
    assert (OLD9 : forall x : word, data <= bv_unsigned x < data + cap -> mem9 x = None)
      by (intros x Hx; rewrite Hout9 by lia; exact (OLD8 x Hx)).
    assert (PR9 : forall b, 0 <= b < 2 ^ 64 -> apresent (w_H W) mem b -> ~ (data <= b < data + cap) -> ~ (O_ <= b < O_ + 56) -> apresent (w_H W') mem9 b)
      by (intros b Hb H1 H2 H3; apply Hpres9, PR8; assumption).
    assert (NB9 : forall b, a <= b < a + ncap -> apresent (w_H W') mem9 b) by (intros b Hb; apply Hpres9, NB8, Hb).
    clear Hout9 Hpres9 EQ8 OLD8 PR8 NB8.
    (* --- unlock and return --- *)
    srun_to HS 0x5669c. intros msR matR HS HF HG. after_run HS HF HG.
    fkeep HF E2 KWR. env_simp_in KWR. rewrite E2 in KWR.
    eapply (SRr_ret_at tfibsegs tbl_app tbl_app_ok Hwx W' _ _ msR _ _ HS); [reflexivity | vm_compute; reflexivity |].
    intros mat'. rewrite ?wvb_collapse. cbv beta.
    apply HK.
    unfold remap_post. cbv zeta. fold len. fold ncap.
    exists a, matN, mat', (ms_regs msR), (ms_mem msR).
    rreg HS (1%bv : bv 5) QR1. env_simp_in QR1. rewrite (ew_seed_reg regs _ _ _ 1 1%bv eq_refl) in QR1.
    split; [exact Hwle|]. split; [exact HwA|]. split; [exact HwH1|]. split; [exact HwH2|].
    split; [exact Hgr|]. split; [lia|]. split; [lia|].
    split; [rewrite QR1; unfold YK0s.ret_ok in Hra; rewrite Hra; reflexivity|].
    split; [apply (regs_preserved_of_st_ok tfibsegs _ _ _ regs [Z_to_bv 64 data; Z_to_bv 64 cap; Z_to_bv 64 size] HS);
            [repeat (apply env_agree_havoc_ge; [lia|]); unfold Eseed; apply env_agree_refl | vm_compute; reflexivity]|].
    split; [intros x H1 H2 H3 H4; rewrite KWR by (unfold AZ; lia); exact (EQ9 x ltac:(unfold AZ; lia) H3 H4)|].
    split; [intros x Hx; rewrite KWR by (unfold AZ, O_; lia); exact (OLD9 x Hx)|].
    split; [intros b Hb H1 H2 H3; apply (apresent_grows _ _ _ _ HG), PR9; assumption|].
    split; [intros b Hb; apply (apresent_grows _ _ _ _ HG), NB9, Hb|].
    split; [memv HS 2%nat 1%nat; [unfold O_; lia | reflexivity | unfold O_; lia]|].
    split; [memv HS 2%nat 0%nat; [unfold O_; lia | reflexivity | lia]|].
    split; [memv HS 0%nat 0%nat; [unfold O_; lia | cbn [sv_denot]; env_simp; rewrite A54, unsigned_lit_small, Z.add_0_r by lia; reflexivity | lia]|].
    split; [memv HS 0%nat 1%nat; [unfold O_; lia | cbn [sv_denot]; env_simp; rewrite A55, unsigned_lit_small, Z.add_0_r by lia; reflexivity | lia]|].
    split; [memv HS 3%nat 0%nat; [unfold O_; lia |
      apply bv_eq; rewrite unsigned_lit_small by lia;
      match goal with |- bv_unsigned (sv_denot ?E ?e) = _ => change (bv_unsigned (sv_denot E e)) with (U E e) end;
      rewrite U_zev by reflexivity; cbn [zev zalu_raw]; unfold rho_of; env_simp; zfin A35 | lia]|].
    split; [cbn [cfg_model] in Hio; apply same_io_wvb3; exact (same_io_wvb2 _ _ _ _ _ _ Hio)|].
    cbn [cfg_model] in Hmw. exact (amwf_same _ _ eq_refl eq_refl Hmw).
Qed.

(* ---------------------------------------------------------------------------------------------------------------- *)
(* 6a. Case 1: the first append (the vector is unmapped) whose string fits the first map (len <= 65536).           *)
Definition first_post (W : world tfibsegs) (regs : bvmap 5 word) (mem : word -> option byte) (md : Model)
  (s : list Z) (W' : world tfibsegs) (c' : config) : Prop :=
  let sp := bv_unsigned (getr regs 2) in let len := Z.of_nat (length s) in let ncap := page_round_up_Z 65536 in
  exists (a : Z) (mat matF : list word) (regs' : bvmap 5 word) (mem' : word -> option byte),
  let mdN := with_vm_backing (m_vm_lazy md) mat md in
  let md1 := Mmap.with_mmap_backing (w64 34) (w64 a) (w64 ncap) (YK0v.mmap_model (w64 a) (w64 ncap) mdN) in
  let mdF := with_vm_backing (m_vm_lazy md1) matF md1 in
  wle W W' /\ w_A W' = w_A W /\
  (forall x : word, a <= bv_unsigned x < a + ncap -> w_H W' x = false) /\
  (forall x : word, ~ (a <= bv_unsigned x < a + ncap) -> w_H W' x = w_H W x) /\
  YK13.grant_ok_na_pin md (w64 a) ncap = true /\ 0 < a /\ a + ncap < 2 ^ 64 /\
  c' = mkCfg (mkst regs' (getr regs 1) mem' (seg_rom tfibsegs)) mdF /\
  regs_preserved regs regs' /\
  (forall x : word, ~ (sp - 512 <= bv_unsigned x < sp) -> ~ (O_ <= bv_unsigned x < O_ + 56) ->
     ~ (a <= bv_unsigned x < a + ncap) -> mem' x = mem x) /\
  (forall b, 0 <= b < 2 ^ 64 -> apresent (w_H W) mem b -> ~ (O_ <= b < O_ + 56) -> apresent (w_H W') mem' b) /\
  (forall b, a <= b < a + ncap -> apresent (w_H W') mem' b) /\
  val_mem tfibsegs (mrestrict (w_H W') mem') O_ 8 (O_ + 32) /\ val_mem tfibsegs (mrestrict (w_H W') mem') (O_ + 16) 8 0 /\
  val_mem tfibsegs (mrestrict (w_H W') mem') (O_ + 32) 8 a /\ val_mem tfibsegs (mrestrict (w_H W') mem') (O_ + 40) 8 ncap /\
  val_mem tfibsegs (mrestrict (w_H W') mem') (O_ + 48) 8 len /\
  same_io md mdF /\ amwf mdF.

Lemma app_first1 : forall {R : Type} (K : Z -> itree astate R) (Q : R -> world tfibsegs -> config -> Prop) (snap : astate) (rq : Z)
  (W : world tfibsegs) (regs : bvmap 5 word) (mem : word -> option byte) (md : Model)
  (p data size : Z) (s : list Z),
  let H := w_H W in let m := mrestrict H mem in let sp := bv_unsigned (getr regs 2) in let len := Z.of_nat (length s) in
  let ncap := page_round_up_Z 65536 in
  sp mod 16 = 0 -> TFIB_IMG_END + 512 <= sp -> (forall a, sp - 512 <= a < sp -> apresent H mem a) ->
  val_mem tfibsegs m O_ 8 0 -> val_mem tfibsegs m (O_ + 16) 8 0 -> val_mem tfibsegs m (O_ + 32) 8 data ->
  val_mem tfibsegs m (O_ + 40) 8 0 -> val_mem tfibsegs m (O_ + 48) 8 size ->
  val_mem tfibsegs m 0x103a0 8 0xafffff00000fffff ->
  getr regs 10 = Z_to_bv 64 p -> sp <= p -> p + len + 1 < 2 ^ 64 -> YK0s.ret_ok (getr regs 1) ->
  (forall i, (i < length s)%nat -> val_mem tfibsegs m (p + Z.of_nat i) 1 (nth i s 0) /\ 0 < nth i s 0 < 256) ->
  val_mem tfibsegs m (p + len) 1 0 ->
  0 <= data < 2 ^ 64 -> 0 <= size < 2 ^ 47 -> len <= 65536 ->
  amwf md ->
  (forall mat, Z.of_nat (length mat) * page_size <= A_bytes (w_A W) ->
     Placement.mmap_grant_refusable (w64 34) (with_vm_backing (m_vm_lazy md) mat md) ncap = false) ->
  (forall a : word, YK13.grant_ok_na_pin md a ncap = true ->
     (bv_unsigned a + ncap <= TFIB_IMG_LO \/ TFIB_IMG_END <= bv_unsigned a) /\
     (bv_unsigned a + ncap <= sp - 512 \/ p + len + 1 <= bv_unsigned a)) ->
  (forall (a2 : Z) (pg : word), YK13.grant_ok_na_pin md (w64 a2) ncap = true -> a2 <= bv_unsigned pg ->
     bv_unsigned pg + page_size <= a2 + ncap -> page_in_ranges pg (m_vm_lazy md) = false) ->
  eager_used md + A_bytes (w_A W) + ncap <= vm_limit (m_vmmaps md) ->
  val_mem tfibsegs m 0x9df30 8 0x1360e0 -> val_mem tfibsegs m 0x1360e0 8 4096 ->
  val_mem tfibsegs m 0x9df40 8 0x138168 -> val_mem tfibsegs m 0x13826c 1 0 -> val_mem tfibsegs m 0x1381f8 8 0 ->
  (forall W' c', first_post W regs mem md s W' c' -> amreal tfibsegs (K 1) W' c' Q) ->
  amreal tfibsegs (IAsk (KMmapSec rq) snap K) W (mkCfg (mkst regs (Z_to_bv 64 0x56418) mem (seg_rom tfibsegs)) md) Q.
Proof.
intros R K Q snap rq W regs mem md p data size s. cbv zeta.
intros Hal Hsp HPRES V0 V16 V32 V40 V48 VK H10 Hp Hp64 Hra HSTR HNUL Hd Hs Hl65 Hamwf HNR HGA HGL HGB VC1 VC2 VC3 VC4 VC5 HK.
apply (amreal_SRr_pre tfibsegs _ _ _ _ (fun W' c' => amreal tfibsegs (IAsk (KMmapSec rq) snap K) W' c' Q)); [|intros W' c' _ X; exact X].
pose proof Hwx_tfa as Hwx. pose proof (u64_range (getr regs 2)) as Usp.
set (len := Z.of_nat (length s)) in *.
assert (Hlen0 : 0 <= len) by lia.
pose proof (seed_ok W regs mem 0 data 0 size Hal Hsp ltac:(intros a Ha; apply HPRES; lia)
  ltac:(lia) Hd ltac:(lia) Hs V0 V16 V32 V40 V48 VK) as HS.
assert (E2 : ew (Eseed regs data 0 size) 2 = getr regs 2) by (exact (ew_seed_reg regs _ _ _ 2 2%bv eq_refl)).
set (sp := bv_unsigned (getr regs 2)) in *.
unfold TFIB_IMG_END, TFIB_IMG_LO in *.
destruct (str_bytes _ p s HSTR HNUL) as [HNZ HRD]. rewrite length_map in HRD.
assert (A35 : True) by exact I.
(* --- lock, the pointer test, the zeroed vector, the first Realloc(65536) --- *)
srun_to HS 0x59e3c. intros ms5 mat5 HS HF HG. after_run HS HF HG.
fkeep HF E2 KW5. rewrite E2 in KW5. fold sp in KW5.
assert (PR5 : forall a, apresent (w_H W) mem a -> apresent (w_H W) (ms_mem ms5) a) by (intros a; apply apresent_grows; exact HG). clear HG.
assert (EQ5 : forall x : word, ~ AZ sp (bv_unsigned x) -> ~ (0 <= bv_unsigned x < 0) -> ms_mem ms5 x = mem x)
  by (intros x Hx _; exact (KW5 x Hx)). clear KW5.
    apply SRr_ret. cbv beta.
    assert (Hvm : forall (x : Z) k, (k < 8)%nat -> 0x9df30 <= x -> x + 8 <= O_ \/ O_ + 56 <= x -> x + 8 <= 0x5fc000 ->
      ms_mem ms5 (Z_to_bv 64 (x + Z.of_nat k)) = mem (Z_to_bv 64 (x + Z.of_nat k))).
    { intros x k Hk H1 H2 H3. apply EQ5; rewrite unsigned_lit_small by lia; unfold AZ, O_ in *; lia. }
    regv HS (10%bv : bv 5) (O_ + 32) Q10 ltac:(unfold O_; zfin A35).
    regv HS (11%bv : bv 5) 65536 Q11 ltac:(zfin A35).
    regv HS (2%bv : bv 5) (sp - 96) Q2 ltac:(rewrite (ew_seed_reg regs _ _ _ 2 2%bv eq_refl); fold sp; zfin A35).
    rreg HS (1%bv : bv 5) Q1.
    lazymatch type of HS with st_ok _ _ ?ss _ =>
      let rs := eval vm_compute in (match ss_mem ss with r0 :: r1 :: _ :: r3 :: r4 :: _ => [r0; r1; r3; r4] | _ => [] end) in
      eapply (RepAppRcf.realloc_stretch K Q snap rq W 35 _ _ rs ms5 _ (O_ + 32) 65536 0 0 0 0x5654c)
    end;
    [ exact HS | reflexivity | reflexivity | vm_compute; reflexivity | vm_compute; reflexivity | vm_compute; reflexivity
    | vm_compute; reflexivity
    | apply submem_keep; [apply subregion_refl|]; apply submem_keep; [apply subregion_refl|]; apply submem_drop;
      apply submem_keep; [apply subregion_refl|]; apply submem_keep; [apply subregion_refl|]; apply submem_nil
    | reflexivity | | | | clear HS ].
    { (* Realloc's premises at the call *)
      unfold RepReallocD.realloc_pre, RepReallocD.REALLOC_STK, RepReallocD.REALLOC_FRAME, RepMmapcf.MOD_STK, TFIB_IMG_LO, TFIB_IMG_END. cbv zeta. rewrite Q2, unsigned_lit_small by lia.
      split; [exact Q10|]. split; [exact Q11|]. split; [rewrite Q1; apply ret_ok_of_mod2; [reflexivity | lia]|].
      split; [apply (amwf_same md); [reflexivity | reflexivity | exact Hamwf]|].
      split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|]. split; [unfold O_; lia|]. split; [unfold O_; lia|].
      split; [reflexivity|].
      split; [first [memv HS 2%nat 0%nat; [unfold O_; lia | reflexivity | lia] | memv HS 2%nat 1%nat; [unfold O_; lia | reflexivity | lia]]|].
      split; [first [memv HS 2%nat 0%nat; [unfold O_; lia | reflexivity | lia] | memv HS 2%nat 1%nat; [unfold O_; lia | reflexivity | lia]]|].
      split; [memv HS 3%nat 0%nat; [unfold O_; lia | reflexivity | lia]|].
      split; [intros x Hx; apply rw_writable; unfold O_ in *; lia|].
      split; [left; unfold O_; lia|]. split; [unfold O_; lia|]. split; [unfold O_; lia|].
      split; [lia|]. split; [unfold TASK_SIZE; lia|].
      split; [left; reflexivity|].
      split; [intros i Hi; lia|].
      split; [lia|]. split; [unfold O_; lia|].
      split; [apply (vm_frameH (w_H W) (w_H W) mem (ms_mem ms5)); [intros k Hk; split; [reflexivity | apply Hvm; unfold O_; lia] | exact VC1]|].
      split; [apply (vm_frameH (w_H W) (w_H W) mem (ms_mem ms5)); [intros k Hk; split; [reflexivity | apply Hvm; unfold O_; lia] | exact VC2]|].
      split; [apply (vm_frameH (w_H W) (w_H W) mem (ms_mem ms5)); [intros k Hk; split; [reflexivity | apply Hvm; unfold O_; lia] | exact VC3]|].
      split; [apply (vm_frameH (w_H W) (w_H W) mem (ms_mem ms5)); [intros k Hk; split; [reflexivity | apply Hvm; unfold O_; cbn in Hk; lia] | exact VC4]|].
      split; [apply (vm_frameH (w_H W) (w_H W) mem (ms_mem ms5)); [intros k Hk; split; [reflexivity | apply Hvm; unfold O_; lia] | exact VC5]|].
      split; [intros mat Hm; rewrite wvb_collapse; exact (HNR mat Hm)|].
      split; [intros a Ha; rewrite grant_wvb in Ha; destruct (HGA a Ha) as [G1 G2]; split; [exact G1|]; split; [lia | unfold O_; lia]|].
      split; [intros a2 pg Ha2 Hpg1 Hpg2; rewrite grant_wvb in Ha2; exact (HGL a2 pg Ha2 Hpg1 Hpg2)|].
      split; [rewrite eager_used_wvb, m_vmmaps_wvb; exact HGB|].
      split; [replace (sp - 96) with (sp + (-6) * 16) by lia; rewrite Z_mod_plus_full; exact Hal|].
      split; [lia|].
      intros b Hb. apply PR5, HPRES. lia. }
    { intros r x Hr Hx. rewrite Q2, unsigned_lit_small by lia. unfold RepReallocD.REALLOC_STK, RepReallocD.REALLOC_FRAME, RepMmapcf.MOD_STK.
      cbn [In] in Hr; repeat (destruct Hr as [<-|Hr]; [cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val] in Hx; env_simp_in Hx; rewrite ?E2 in Hx; unfold O_ in *; lia|]); destruct Hr. }
    { intros r x Hr Hx a Ha. rewrite grant_wvb in Ha. destruct (HGA a Ha) as [G1 G2].
      cbn [In] in Hr; repeat (destruct Hr as [<-|Hr]; [cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val] in Hx; env_simp_in Hx; rewrite ?E2 in Hx; unfold O_ in *; lia|]); destruct Hr. }
    intros W' regs' mem' mdx HP HS.
    set (ncap := page_round_up_Z 65536) in *.
    assert (NC65 : ncap = 65536) by reflexivity.
    unfold RepReallocD.realloc_post in HP. cbv zeta in HP. rewrite Q2, unsigned_lit_small in HP by lia.
    unfold RepReallocD.REALLOC_STK, RepReallocD.REALLOC_FRAME, RepMmapcf.MOD_STK in HP.
    destruct HP as (a & regsR & memR & matN & matM & Hwle & HwA & HwH1 & HwH2 & Hgr & Ha0 & Ha1 & Hc' & Hrp & VA & VC & VS &
      Hcp & Hz & Hold & FRr & PRr & NBr & Hio & Hmw).
    clear Q10 Q11 Q1 Q2.
    assert (Emem : mem' = memR) by (apply (f_equal (fun c => ms_mem (cfg_ms c))) in Hc'; exact Hc').
    pose proof (f_equal cfg_model Hc') as Emd. cbn [cfg_model] in Emd.
    subst mem' mdx. rewrite !wvb_collapse in *. clear Hc'.
    rewrite grant_wvb in Hgr.
    assert (Ua : bv_unsigned (w64 a) = a) by (unfold w64; apply unsigned_lit_small; lia).
    destruct (HGA (w64 a) Hgr) as [GA1 GA2]. rewrite Ua in GA1, GA2.
    assert (EQR : forall x : word, ~ AZ sp (bv_unsigned x) -> ~ (a <= bv_unsigned x < a + ncap) -> memR x = mem x).
    { intros x H1 H2. rewrite FRr by (unfold AZ, O_ in *; lia). apply EQ5; [exact H1 | lia]. }
    assert (PRR : forall b, 0 <= b < 2 ^ 64 -> apresent (w_H W) mem b -> ~ (O_ <= b < O_ + 56) -> apresent (w_H W') memR b).
    { intros b Hb Hp1 Hn2. apply PRr; [lia | apply PR5, Hp1 | lia | unfold O_ in *; lia]. }
    clear FRr PRr EQ5 PR5 Hvm.
    apply (st_ok_havoc_ext 51 _ _ _ [Z_to_bv 64 a; Z_to_bv 64 ncap]) in HS; [| vm_compute; reflexivity].
    assert (A51 : forall E, ew (havoc E 51 [Z_to_bv 64 a; Z_to_bv 64 ncap]) 51 = Z_to_bv 64 a)
      by (intros E; exact (ew_havoc_new E 51 [Z_to_bv 64 a; Z_to_bv 64 ncap] 0 (Z_to_bv 64 0) ltac:(apply Nat.ltb_lt; reflexivity))).
    assert (A52 : forall E, ew (havoc E 51 [Z_to_bv 64 a; Z_to_bv 64 ncap]) 52 = Z_to_bv 64 ncap)
      by (intros E; exact (ew_havoc_new E 51 [Z_to_bv 64 a; Z_to_bv 64 ncap] 1 (Z_to_bv 64 0) ltac:(apply Nat.ltb_lt; reflexivity))).
    apply (st_ok_add_region _ _ _ (YP09.mkRegion None (O_ + 32) (O_ + 48) (O_ + 32) (O_ + 48)
      [YP09.mkChunk (O_ + 32) (CVal 8 (SOff 51 0)); YP09.mkChunk (O_ + 40) (CVal 8 (SOff 52 0))])) in HS;
    [ | reflexivity
    | unfold region_ok; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val ms_mem restrict mkst];
      unfold O_; split; [lia|]; split; [lia|]; split; [intros o Ho; apply rw_writable; lia|];
      apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]];
      [ apply (chunk_ok_val tfibsegs _ _ _ _ _ _ a); [cbn [sv_denot]; rewrite A51, unsigned_lit_small, Z.add_0_r by lia; reflexivity | cbn; lia | cbn; lia | rewrite Z.add_0_l; exact VA]
      | apply (chunk_ok_val tfibsegs _ _ _ _ _ _ ncap); [cbn [sv_denot]; rewrite A52, unsigned_lit_small, Z.add_0_r by lia; reflexivity | cbn; lia | cbn; lia | rewrite Z.add_0_l; exact VC] ]
    | cbn [all_disjoint ss_mem ss_after_call]; unfold extent_disjoint; cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val]; env_simp; rewrite E2; unfold O_; repeat split; lia ].
    cbn [ss_pc ss_regs ss_mem ss_resv ss_facts] in HS.
    apply (amreal_SRr_pre tfibsegs _ _ _ _ (fun W2 c2 => amreal tfibsegs (K 1) W2 c2 Q)); [|intros W2 c2 _ X; exact X].
    (* --- internal_strlen, now in the exposed world --- *)
    srun_to HS 0x653b0. intros ms6 mat6 HS HF HG. after_run HS HF HG.
    fkeep HF E2 KW6. env_simp_in KW6. rewrite E2 in KW6.
    assert (EQ6 : forall x : word, ~ AZ sp (bv_unsigned x) -> ~ (a <= bv_unsigned x < a + ncap) -> ms_mem ms6 x = mem x)
      by (intros x H1 H2; rewrite (KW6 x H1); exact (EQR x H1 H2)).
    assert (PR6 : forall b, 0 <= b < 2 ^ 64 -> apresent (w_H W) mem b -> ~ (O_ <= b < O_ + 56) -> apresent (w_H W') (ms_mem ms6) b)
      by (intros b Hb H1 H2; apply (apresent_grows _ _ _ _ HG), PRR; assumption).
    assert (NB6 : forall b, a <= b < a + ncap -> apresent (w_H W') (ms_mem ms6) b) by (intros b Hb; apply (apresent_grows _ _ _ _ HG), NBr, Hb).
    clear KW6 HG EQR PRR NBr.
    regv HS (10%bv : bv 5) p Q10 ltac:(rewrite (ew_seed_reg regs _ _ _ 10 10%bv eq_refl), H10; rewrite unsigned_lit_small by lia; unfold zcanon, M64; rewrite Z.add_0_r, Z.mod_small by lia; reflexivity).
    rreg HS (1%bv : bv 5) Q1.
    eapply (istrlen_stretch_gen W' 53 _ _ _ _ p 0x56558 (map (Z_to_bv 8) s));
    [ exact HS | reflexivity | reflexivity | vm_compute; reflexivity | vm_compute; reflexivity | exact Q10 | exact Q1
    | lia | rewrite length_map; lia | exact HNZ | | reflexivity | lia | clear HS Q10 Q1 ].
    { intros j Hj. rewrite length_map in Hj.
      rewrite (mbyte_H (w_H W) (w_H W') mem (ms_mem ms6)); [apply HRD; exact Hj | |].
      - apply HwH2. rewrite unsigned_lit_small by lia. lia.
      - apply EQ6; rewrite unsigned_lit_small by lia; unfold AZ, O_; lia. }
    intros regs7 mat7 HS R10 _. rewrite wvb_collapse. rewrite length_map in R10. fold len in R10.
    assert (A53 : forall E, ew (havoc E 53 (map (getr regs7) [10%bv; 11%bv; 12%bv])) 53 = Z_to_bv 64 len)
      by (intros E; rewrite <- R10; exact (ew_havoc_new E 53 (map (getr regs7) [10%bv; 11%bv; 12%bv]) 0 (Z_to_bv 64 0) ltac:(apply Nat.ltb_lt; reflexivity))).
    (* --- the room tests --- *)
    srun HS. intros ms8 mat8 HS HF HG. after_run HS HF HG.
    fkeep HF E2 KW8. env_simp_in KW8. rewrite E2 in KW8.
    assert (EQ8 : forall x : word, ~ AZ sp (bv_unsigned x) -> ~ (a <= bv_unsigned x < a + ncap) -> ms_mem ms8 x = mem x)
      by (intros x H1 H2; rewrite (KW8 x H1); exact (EQ6 x H1 H2)).
    assert (PR8 : forall b, 0 <= b < 2 ^ 64 -> apresent (w_H W) mem b -> ~ (O_ <= b < O_ + 56) -> apresent (w_H W') (ms_mem ms8) b)
      by (intros b Hb H1 H2; apply (apresent_grows _ _ _ _ HG), PR6; assumption).
    assert (NB8 : forall b, a <= b < a + ncap -> apresent (w_H W') (ms_mem ms8) b) by (intros b Hb; apply (apresent_grows _ _ _ _ HG), NB6, Hb).
    clear KW8 HG EQ6 PR6 NB6.
    srr_branch_sh tbl_app_ok HS.
    + brnorm2 Hc A53 A52. apply negb_true_iff, Z.ltb_ge in Hc. assert (L0 : len = 0) by lia.
      srun_to HS 0x651e0. intros ms9 mat9 HS HF HG. after_run HS HF HG.
      fkeep HF E2 KW9. env_simp_in KW9. rewrite E2 in KW9.
      assert (EQm : forall x : word, ~ AZ sp (bv_unsigned x) -> ~ (a <= bv_unsigned x < a + ncap) -> ms_mem ms9 x = mem x)
        by (intros x H1 H2; rewrite (KW9 x H1); exact (EQ8 x H1 H2)).
      assert (PRm : forall b, 0 <= b < 2 ^ 64 -> apresent (w_H W) mem b -> ~ (O_ <= b < O_ + 56) -> apresent (w_H W') (ms_mem ms9) b)
        by (intros b Hb H1 H2; apply (apresent_grows _ _ _ _ HG), PR8; assumption).
      assert (NBm : forall b, a <= b < a + ncap -> apresent (w_H W') (ms_mem ms9) b) by (intros b Hb; apply (apresent_grows _ _ _ _ HG), NB8, Hb).
      clear KW9 HG EQ8 PR8 NB8.
      regv HS (10%bv : bv 5) a Q10 ltac:(rewrite ?A51, ?A52; zfin A53).
      regv HS (11%bv : bv 5) p Q11 ltac:(rewrite (ew_seed_reg regs _ _ _ 10 10%bv eq_refl), H10; zfin A53).
      regv HS (12%bv : bv 5) len Q12 ltac:(zfin A53).
      rreg HS (1%bv : bv 5) Q1.
      eapply (imemcpy_stretch_gen W' 56 _ _ _ _ a p len 0x565b4 (map (Z_to_bv 8) s));
      [ exact HS | reflexivity | reflexivity | vm_compute; reflexivity | vm_compute; reflexivity
      | exact Q10 | exact Q11 | exact Q12 | exact Q1 | rewrite length_map; reflexivity
      | lia | lia | lia | lia | lia | | | reflexivity | lia | hext E2 | hext64 E2 | clear HS Q10 Q11 Q12 Q1 ].
      { intros b Hb. apply NBm. lia. }
      { intros j Hj. rewrite length_map in Hj.
        rewrite (mbyte_H (w_H W) (w_H W') mem (ms_mem ms9)); [rewrite (HRD j ltac:(lia)), app_nth1 by (rewrite length_map; exact Hj); reflexivity | |].
        - apply HwH2. rewrite unsigned_lit_small by lia. lia.
        - apply EQm; rewrite unsigned_lit_small by lia; unfold AZ, O_; lia. }
      intros regsZ memZ matZ HS _ _ HoutZ HpresZ _. rewrite wvb_collapse.
      assert (EQZ : forall x : word, ~ AZ sp (bv_unsigned x) -> ~ (a <= bv_unsigned x < a + ncap) -> memZ x = mem x)
        by (intros x H1 H2; rewrite HoutZ by lia; exact (EQm x H1 H2)).
      assert (PRZ : forall b, 0 <= b < 2 ^ 64 -> apresent (w_H W) mem b -> ~ (O_ <= b < O_ + 56) -> apresent (w_H W') memZ b)
        by (intros b Hb H1 H2; apply HpresZ, PRm; assumption).
      assert (NBZ : forall b, a <= b < a + ncap -> apresent (w_H W') memZ b) by (intros b Hb; apply HpresZ, NBm, Hb).
      clear HoutZ HpresZ EQm PRm NBm.
      srun_to HS 0x5669c. intros msR matR HS HF HG. after_run HS HF HG.
      fkeep HF E2 KWR. env_simp_in KWR. rewrite E2 in KWR.
      eapply (SRr_ret_at tfibsegs tbl_app tbl_app_ok Hwx W' _ _ msR _ _ HS); [reflexivity | vm_compute; reflexivity |].
      intros mat'. rewrite ?wvb_collapse. cbv beta.
      apply HK.
      unfold first_post. cbv zeta. fold len. fold ncap.
      exists a, matN, mat', (ms_regs msR), (ms_mem msR).
      rreg HS (1%bv : bv 5) QR1. env_simp_in QR1. rewrite (ew_seed_reg regs _ _ _ 1 1%bv eq_refl) in QR1.
      split; [exact Hwle|]. split; [exact HwA|]. split; [exact HwH1|]. split; [exact HwH2|].
      split; [exact Hgr|]. split; [lia|]. split; [lia|].
      split; [rewrite QR1; unfold YK0s.ret_ok in Hra; rewrite Hra; reflexivity|].
      split; [apply (regs_preserved_of_st_ok tfibsegs _ _ _ regs [Z_to_bv 64 data; Z_to_bv 64 0; Z_to_bv 64 size] HS);
              [repeat (apply env_agree_havoc_ge; [lia|]); unfold Eseed; apply env_agree_refl | vm_compute; reflexivity]|].
      split; [intros x H1 H2 H3; rewrite KWR by (unfold AZ; lia); exact (EQZ x ltac:(unfold AZ; lia) H3)|].
      split; [intros b Hb H1 H2; apply (apresent_grows _ _ _ _ HG), PRZ; assumption|].
      split; [intros b Hb; apply (apresent_grows _ _ _ _ HG), NBZ, Hb|].
      split; [first [memv HS 2%nat 1%nat; [unfold O_; lia | reflexivity | unfold O_; lia] | memv HS 2%nat 0%nat; [unfold O_; lia | reflexivity | unfold O_; lia]]|].
      split; [first [memv HS 2%nat 0%nat; [unfold O_; lia | reflexivity | lia] | memv HS 2%nat 1%nat; [unfold O_; lia | reflexivity | lia]]|].
      split; [memv HS 0%nat 0%nat; [unfold O_; lia | cbn [sv_denot]; env_simp; rewrite A51, unsigned_lit_small, Z.add_0_r by lia; reflexivity | lia]|].
      split; [memv HS 0%nat 1%nat; [unfold O_; lia | cbn [sv_denot]; env_simp; rewrite A52, unsigned_lit_small, Z.add_0_r by lia; reflexivity | lia]|].
      split; [memv HS 3%nat 0%nat; [unfold O_; lia |
        apply bv_eq; rewrite unsigned_lit_small by lia;
        match goal with |- bv_unsigned (sv_denot ?E ?e) = _ => change (bv_unsigned (sv_denot E e)) with (U E e) end;
        rewrite U_zev by reflexivity; cbn [zev zalu_raw]; unfold rho_of; env_simp; zfin A53 | lia]|].
      split; [cbn [cfg_model] in Hio; apply same_io_wvb3; exact (same_io_wvb2 _ _ _ _ _ _ Hio)|].
      cbn [cfg_model] in Hmw. exact (amwf_same _ _ eq_refl eq_refl Hmw).
    + brnorm2 Hc A53 A52. apply negb_false_iff, Z.ltb_lt in Hc.
      srun HS. intros ms9 mat9 HS HF HG. after_run HS HF HG.
      fkeep HF E2 KW9. env_simp_in KW9. rewrite E2 in KW9.
      assert (EQ9a : forall x : word, ~ AZ sp (bv_unsigned x) -> ~ (a <= bv_unsigned x < a + ncap) -> ms_mem ms9 x = mem x)
        by (intros x H1 H2; rewrite (KW9 x H1); exact (EQ8 x H1 H2)).
      assert (PR9a : forall b, 0 <= b < 2 ^ 64 -> apresent (w_H W) mem b -> ~ (O_ <= b < O_ + 56) -> apresent (w_H W') (ms_mem ms9) b)
        by (intros b Hb H1 H2; apply (apresent_grows _ _ _ _ HG), PR8; assumption).
      assert (NB9a : forall b, a <= b < a + ncap -> apresent (w_H W') (ms_mem ms9) b) by (intros b Hb; apply (apresent_grows _ _ _ _ HG), NB8, Hb).
      clear KW9 HG EQ8 PR8 NB8.
      srr_branch_sh tbl_app_ok HS.
      * brnorm2 Hc0 A53 A52. apply negb_true_iff, Z.ltb_ge in Hc0.
        srun_to HS 0x6525c. intros ms10 mat10 HS HF HG. after_run HS HF HG.
        fkeep HF E2 KW10. env_simp_in KW10. rewrite E2 in KW10.
        assert (EQ10 : forall x : word, ~ AZ sp (bv_unsigned x) -> ~ (a <= bv_unsigned x < a + ncap) -> ms_mem ms10 x = mem x)
          by (intros x H1 H2; rewrite (KW10 x H1); exact (EQ9a x H1 H2)).
        assert (PR10 : forall b, 0 <= b < 2 ^ 64 -> apresent (w_H W) mem b -> ~ (O_ <= b < O_ + 56) -> apresent (w_H W') (ms_mem ms10) b)
          by (intros b Hb H1 H2; apply (apresent_grows _ _ _ _ HG), PR9a; assumption).
        assert (NB10 : forall b, a <= b < a + ncap -> apresent (w_H W') (ms_mem ms10) b) by (intros b Hb; apply (apresent_grows _ _ _ _ HG), NB9a, Hb).
        clear KW10 HG EQ9a PR9a NB9a.
        regv HS (10%bv : bv 5) a Q10 ltac:(rewrite ?A51, ?A52; zfin A53).
        regv HS (11%bv : bv 5) 0 Q11 ltac:(zfin A53).
        regv HS (12%bv : bv 5) len Q12 ltac:(zfin A53).
        rreg HS (1%bv : bv 5) Q1.
        eapply (imemset_stretch_gen W' 56 _ _ _ _ a len 0x56598);
        [ exact HS | reflexivity | reflexivity | vm_compute; reflexivity | vm_compute; reflexivity
        | exact Q10 | exact Q11 | exact Q12 | exact Q1 | lia | lia | lia | | reflexivity | lia | hext E2 | hext64 E2
        | clear HS Q10 Q11 Q12 Q1 ].
        { intros b Hb. apply NB10. lia. }
        intros regs11 mem11 mat11 HS _ _ Hout11 Hpres11 _. rewrite wvb_collapse.
        assert (EQm : forall x : word, ~ AZ sp (bv_unsigned x) -> ~ (a <= bv_unsigned x < a + ncap) -> mem11 x = mem x)
          by (intros x H1 H2; rewrite Hout11 by lia; exact (EQ10 x H1 H2)).
        assert (PRm : forall b, 0 <= b < 2 ^ 64 -> apresent (w_H W) mem b -> ~ (O_ <= b < O_ + 56) -> apresent (w_H W') mem11 b)
          by (intros b Hb H1 H2; apply Hpres11, PR10; assumption).
        assert (NBm : forall b, a <= b < a + ncap -> apresent (w_H W') mem11 b) by (intros b Hb; apply Hpres11, NB10, Hb).
        clear Hout11 Hpres11 EQ10 PR10 NB10.
        srun_to HS 0x651e0. intros ms12 mat12 HS HF HG. after_run HS HF HG.
        fkeep HF E2 KW12. env_simp_in KW12. rewrite E2 in KW12.
        assert (EQn : forall x : word, ~ AZ sp (bv_unsigned x) -> ~ (a <= bv_unsigned x < a + ncap) -> ms_mem ms12 x = mem x)
          by (intros x H1 H2; rewrite (KW12 x H1); exact (EQm x H1 H2)).
        assert (PRn : forall b, 0 <= b < 2 ^ 64 -> apresent (w_H W) mem b -> ~ (O_ <= b < O_ + 56) -> apresent (w_H W') (ms_mem ms12) b)
          by (intros b Hb H1 H2; apply (apresent_grows _ _ _ _ HG), PRm; assumption).
        assert (NBn : forall b, a <= b < a + ncap -> apresent (w_H W') (ms_mem ms12) b) by (intros b Hb; apply (apresent_grows _ _ _ _ HG), NBm, Hb).
        clear KW12 HG EQm PRm NBm.
        regv HS (10%bv : bv 5) a Q10 ltac:(rewrite ?A51, ?A52; zfin A53).
        regv HS (11%bv : bv 5) p Q11 ltac:(rewrite (ew_seed_reg regs _ _ _ 10 10%bv eq_refl), H10; zfin A53).
        regv HS (12%bv : bv 5) len Q12 ltac:(zfin A53).
        rreg HS (1%bv : bv 5) Q1.
        eapply (imemcpy_stretch_gen W' 59 _ _ _ _ a p len 0x565b4 (map (Z_to_bv 8) s));
        [ exact HS | reflexivity | reflexivity | vm_compute; reflexivity | vm_compute; reflexivity
        | exact Q10 | exact Q11 | exact Q12 | exact Q1 | rewrite length_map; reflexivity
        | lia | lia | lia | lia | lia | | | reflexivity | lia | hext E2 | hext64 E2 | clear HS Q10 Q11 Q12 Q1 ].
        { intros b Hb. apply NBn. lia. }
        { intros j Hj. rewrite length_map in Hj.
          rewrite (mbyte_H (w_H W) (w_H W') mem (ms_mem ms12)); [rewrite (HRD j ltac:(lia)), app_nth1 by (rewrite length_map; exact Hj); reflexivity | |].
          - apply HwH2. rewrite unsigned_lit_small by lia. lia.
          - apply EQn; rewrite unsigned_lit_small by lia; unfold AZ, O_; lia. }
        intros regsZ memZ matZ HS _ _ HoutZ HpresZ _. rewrite wvb_collapse.
        assert (EQZ : forall x : word, ~ AZ sp (bv_unsigned x) -> ~ (a <= bv_unsigned x < a + ncap) -> memZ x = mem x)
          by (intros x H1 H2; rewrite HoutZ by lia; exact (EQn x H1 H2)).
        assert (PRZ : forall b, 0 <= b < 2 ^ 64 -> apresent (w_H W) mem b -> ~ (O_ <= b < O_ + 56) -> apresent (w_H W') memZ b)
          by (intros b Hb H1 H2; apply HpresZ, PRn; assumption).
        assert (NBZ : forall b, a <= b < a + ncap -> apresent (w_H W') memZ b) by (intros b Hb; apply HpresZ, NBn, Hb).
        clear HoutZ HpresZ EQn PRn NBn.
        srun_to HS 0x5669c. intros msR matR HS HF HG. after_run HS HF HG.
        fkeep HF E2 KWR. env_simp_in KWR. rewrite E2 in KWR.
        eapply (SRr_ret_at tfibsegs tbl_app tbl_app_ok Hwx W' _ _ msR _ _ HS); [reflexivity | vm_compute; reflexivity |].
        intros mat'. rewrite ?wvb_collapse. cbv beta.
        apply HK.
        unfold first_post. cbv zeta. fold len. fold ncap.
        exists a, matN, mat', (ms_regs msR), (ms_mem msR).
        rreg HS (1%bv : bv 5) QR1. env_simp_in QR1. rewrite (ew_seed_reg regs _ _ _ 1 1%bv eq_refl) in QR1.
        split; [exact Hwle|]. split; [exact HwA|]. split; [exact HwH1|]. split; [exact HwH2|].
        split; [exact Hgr|]. split; [lia|]. split; [lia|].
        split; [rewrite QR1; unfold YK0s.ret_ok in Hra; rewrite Hra; reflexivity|].
        split; [apply (regs_preserved_of_st_ok tfibsegs _ _ _ regs [Z_to_bv 64 data; Z_to_bv 64 0; Z_to_bv 64 size] HS);
                [repeat (apply env_agree_havoc_ge; [lia|]); unfold Eseed; apply env_agree_refl | vm_compute; reflexivity]|].
        split; [intros x H1 H2 H3; rewrite KWR by (unfold AZ; lia); exact (EQZ x ltac:(unfold AZ; lia) H3)|].
        split; [intros b Hb H1 H2; apply (apresent_grows _ _ _ _ HG), PRZ; assumption|].
        split; [intros b Hb; apply (apresent_grows _ _ _ _ HG), NBZ, Hb|].
        split; [first [memv HS 2%nat 1%nat; [unfold O_; lia | reflexivity | unfold O_; lia] | memv HS 2%nat 0%nat; [unfold O_; lia | reflexivity | unfold O_; lia]]|].
        split; [first [memv HS 2%nat 0%nat; [unfold O_; lia | reflexivity | lia] | memv HS 2%nat 1%nat; [unfold O_; lia | reflexivity | lia]]|].
        split; [memv HS 0%nat 0%nat; [unfold O_; lia | cbn [sv_denot]; env_simp; rewrite A51, unsigned_lit_small, Z.add_0_r by lia; reflexivity | lia]|].
        split; [memv HS 0%nat 1%nat; [unfold O_; lia | cbn [sv_denot]; env_simp; rewrite A52, unsigned_lit_small, Z.add_0_r by lia; reflexivity | lia]|].
        split; [memv HS 3%nat 0%nat; [unfold O_; lia |
          apply bv_eq; rewrite unsigned_lit_small by lia;
          match goal with |- bv_unsigned (sv_denot ?E ?e) = _ => change (bv_unsigned (sv_denot E e)) with (U E e) end;
          rewrite U_zev by reflexivity; cbn [zev zalu_raw]; unfold rho_of; env_simp; zfin A53 | lia]|].
        split; [cbn [cfg_model] in Hio; apply same_io_wvb3; exact (same_io_wvb2 _ _ _ _ _ _ Hio)|].
        cbn [cfg_model] in Hmw. exact (amwf_same _ _ eq_refl eq_refl Hmw).
      * brnorm2 Hc0 A53 A52. apply negb_false_iff, Z.ltb_lt in Hc0. rewrite NC65 in Hc0. lia.
Qed.
End r.
End s.

(* ---------------------------------------------------------------------------------------------------------------- *)
(* 6. The theorem.  The model tree is reduced with RepAppcf's lemmas; case 3 is app_keep, case 4 is app_grow; the
   cases and relation posts not yet written here are named Section hypotheses, prefixed H_, listed in the report. *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YGcfNames YG01cf YG00cf YG0ncf YG0dcf YGcfXs YG06bcf.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import YGcfInstBase.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import RepIFcf.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require RepAppcf RepAppPcf RepAppXcf RepRelcf.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YGcfTok.
From Stdlib Require Import List.
Import ListNotations.

Section t. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {ci : CfImg} {cp : CfParams}.
Variable B : asyms.

Lemma apresent_of_aview_off : forall (H : word -> bool) mem a, off_img a -> aview tfibsegs H mem a <> None -> apresent H mem a.
Proof.
intros H mem a Ha HV. unfold aview in HV. destruct (mbyte tfibsegs (mrestrict H mem) a) as [b|] eqn:E; [|exfalso; exact (HV eq_refl)].
unfold mbyte, mrestrict in E. destruct (H (Z_to_bv 64 a)) eqn:Hh.
- rewrite (seg_rom_none_off a Ha) in E. discriminate.
- destruct (mem (Z_to_bv 64 a)) as [b'|] eqn:Em; [split; [exact Hh | exists b'; exact Em] | rewrite (seg_rom_none_off a Ha) in E; discriminate].
Qed.


Hypothesis errb_map_fits_cf :
  forall (Hp : list Z) (ly : alayout) (S : astate) (W : world tfibsegs) (mem : word -> option byte)
    (md : Model) (nZ : Z),
  layout_ok ly -> img_cover ly -> TfibSyms B -> ly_tsd ly = TFIB_TSD ->
  ARcf tfibsegs B ly S Hp W mem md -> xs_mapped_cf ly S md -> qloose S -> cf_hull_ok S ->
  0 < nZ -> nZ mod kPage = 0 -> nZ <= cf_nob ->
  (exists a, YK13.grant_ok_na_pin md a nZ = true) /\
  eager_used md + A_bytes (w_A W) + nZ <= vm_limit (m_vmmaps md).

(* H_glazy: GLAZY of RepReallocD.realloc_pre at an errbuf call (RepF4Append's finding 7, carried upward). *)
Hypothesis H_glazy : forall lk Hp ly S W mem md n, errb_call_pre B lk Hp ly S W mem md -> 0 < n -> n mod 4096 = 0 ->
  forall (a2 : Z) (pg : word), YK13.grant_ok_na_pin md (w64 a2) n = true -> a2 <= bv_unsigned pg ->
  bv_unsigned pg + page_size <= a2 + n -> page_in_ranges pg (m_vm_lazy md) = false.

(* H_aledger: a Theorem Labs lane's new alc_eager_x (RepRelcf.ALEDGER_X) at an errbuf call; RepF4Append carries it upward. *)
Hypothesis H_aledger : forall lk Hp ly S W mem md, errb_call_pre B lk Hp ly S W mem md -> RepRelcf.ALEDGER_X ly S md.

(* H_pfa: the layer's unit row YG0ncf.pf_cells_apart_t (field round 3; not an ARmcf field) at the unit's symbols, whose
   third conjunct keeps Printf's cells apart from the errbuf object (RepRelXcf.pf_errb_apart), for amc_pf_cells across
   the object writes; at cgif YGcfImgcgif.pf_cells_apart_cgif. *)
Hypothesis H_pfa : TfibSyms B -> pf_cells_apart_t B.

(* The model state after one granted errbuf map keeps the WfP_cf carry of the entry (YG06bcf.errb_map_cf_ok). *)
Lemma map_S1_wf : forall U (want : Z) (s : astate) snap (S1 : astate) (k : Z -> itree astate (unit * astate)),
  WfP_cf U 0 (errb_slack s) 0 s -> 0 < want -> round_up want kPage <= cf_nob ->
  errb_map_cf want s = IAsk (KMmapSec (round_up want kPage)) snap k -> (forall z, z <> 0 -> k z = IRet (tt, S1)) ->
  WfP_cf U 0 (errb_slack S1) 0 S1.
Proof.
intros U want s snap S1 k Hw Hpos Hr Hask Hk.
pose proof (errb_map_cf_ok U 0 (errb_slack s) 0 s want true Hw Hpos Hr) as A. rewrite Hask in A.
cbn [atok_cf] in A. destruct A as [_ A]. specialize (A 1 (or_intror eq_refl)). rewrite (Hk 1 ltac:(discriminate)) in A.
cbn [atok_cf snd] in A. destruct A as (W1 & _ & _ & _ & _ & F). unfold errb_slack. rewrite F. exact W1.
Qed.

Lemma filter_existsb_false : forall (f : secmap -> bool) l, existsb f l = false -> filter f l = [].
Proof.
intros f l. induction l as [|x l IH]; cbn; [reflexivity|]. intros H. apply orb_false_iff in H as [H1 H2]. rewrite H1. exact (IH H2).
Qed.
Lemma cap_unmapped : forall S, errb_mapped_cf S = false -> errb_cap_cf S = 0.
Proof. intros S H. unfold errb_cap_cf, errb_e. unfold errb_mapped_cf in H. rewrite (filter_existsb_false _ _ H). reflexivity. Qed.
Lemma cap_after_map : forall S S1 n, st_secs S1 = map cfx_retire (st_secs S) ++ [mkSec n ERRB_CAP_TAG false] -> errb_cap_cf S1 = Z.max 0 n.
Proof. intros S S1 n E. unfold errb_cap_cf, errb_e. rewrite E, filter_app, YGcfXs.cfx_filter_retired. reflexivity. Qed.

(* Case 1: the first append of a string that fits the first map. *)
Lemma app_case1 : forall (R : Type) (Hp : list Z) (ly : alayout) (S : astate) (W : world tfibsegs) (regs : bvmap 5 word)
  (mem : word -> option byte) (md : Model) (p : Z) (s : list Z) (lk : option Z)
  (K : astate -> itree astate R) (Q : R -> world tfibsegs -> config -> Prop),
errb_mapped_cf S = false -> Z.of_nat (length s) <= 65536 ->
errb_call_pre B lk Hp ly S W mem md -> errb_room_for S (Z.of_nat (length s)) -> errb_call_regs B APP_STK ly W regs mem ->
getr regs 10 = w64 p -> spZ regs <= p -> p + Z.of_nat (length s) + 1 <= ly_stk_hi ly ->
(forall i, (i < length s)%nat -> val_mem tfibsegs (mrestrict (w_H W) mem) (p + Z.of_nat i) 1 (nth i s 0) /\ 0 < nth i s 0 < 256) ->
val_mem tfibsegs (mrestrict (w_H W) mem) (p + Z.of_nat (length s)) 1 0 ->
(forall S' W' c', errb_call_post B lk APP_STK (Z.of_nat (length s)) Hp ly S S' W regs mem md W' c' -> amreal tfibsegs (K S') W' c' Q) ->
amreal tfibsegs (ibind (errb_append_cf (Z.of_nat (length s)) S) (fun r => K (snd r)))
  W (cfg_at tfibsegs A_APPEND regs mem md) Q.
Proof.
intros R Hp ly S W regs mem md p s lk K Q EM L65 PRE ROOM REGS H10 Hp1 Hp2 HSTR HNUL HK.
pose proof (RepAppcf.rep_pre_cells B lk Hp ly S W mem md PRE) as (C0 & C16 & C32 & C40 & C48 & CV & Csc & Cal).
rewrite EM in C0.
destruct (RepAppXcf.app_apart_of_pre B lk Hp ly S W mem md regs PRE REGS) as (Hhigh & Hstk & Hs0 & Hnob & Hc47 & Hd0 & Hdts & Hd64 & Hmap & Hbuf & Hgr & VK & VC1 & VC2 & VC3 & VC4 & VC5).
clear Hmap Hbuf.
pose proof REGS as (_ & _ & Hra & _ & Hal & Hlo & Hhi & Hwin).
pose proof PRE as (_ & _ & LY & IMG & TS & TSD & (_ & AR & _) & XM & WFP & QL & _ & _ & _ & HT).
pose proof AR as (_ & _ & _ & AMW & _).
pose proof (cap_unmapped S EM) as CAP0. rewrite CAP0 in C40, Csc, Hd64.
pose proof RepAppcf.rep_ncap_init as NI.
assert (RI : round_up ERRB_INIT kPage = page_round_up_Z 65536) by reflexivity.
assert (NC : page_round_up_Z 65536 = 65536) by reflexivity.
assert (NI' : page_round_up_Z 65536 <= cf_nob) by (rewrite <- RI; exact NI).
assert (NCP : 0 < page_round_up_Z 65536) by (rewrite NC; lia).
assert (NCA : page_round_up_Z 65536 mod 4096 = 0) by (rewrite NC; reflexivity).
destruct (errb_map_fits_cf Hp ly S W _ md (page_round_up_Z 65536) LY IMG TS TSD AR XM QL HT NCP NCA NI') as [_ GB].
rewrite (RepAppcf.rep_append_unmapped (Z.of_nat (length s)) S EM).
destruct (RepAppcf.rep_map_ask (ci := ci) ERRB_INIT S) as (snap & S1 & k & Hask & Hk1 & Hfr & Hsec).
assert (WF1 : WfP_cf (as_universe B) 0 (errb_slack S1) 0 S1)
  by exact (map_S1_wf (as_universe B) ERRB_INIT S snap S1 k WFP ltac:(unfold ERRB_INIT; lia) NI Hask Hk1).
assert (C1 : errb_cap_cf S1 = 65536) by (rewrite (cap_after_map S S1 _ Hsec); reflexivity).
rewrite Hask. cbn [ibind]. rewrite RI.
unfold APP_STK, spZ in *. unfold errb_room_for, kPage in ROOM.
unfold cfg_at, A_APPEND, w64.
eapply (app_first1 _ Q snap (page_round_up_Z 65536) W regs mem md p (YG0ncf.errb_data_cf ly S) (errb_size_cf S) s);
[ exact Hal | lia | intros a Ha; apply Hwin; lia | exact C0 | exact C16 | exact C32 | exact C40 | exact C48 | exact VK
| exact H10 | exact Hp1 | lia | exact Hra | exact HSTR | exact HNUL | lia | lia | exact L65 | exact AMW
| intros mat Hm; exact (RepAppcf.errb_map_not_refusable B errb_map_fits_cf Hp ly S W _ md mat _ LY IMG TS TSD AR XM QL HT NCP NCA NI' Hm)
| intros a Ha; destruct (Hgr a _ NCP NCA Ha) as [G1 G2]; split; [exact G1 | lia]
| exact (H_glazy lk Hp ly S W mem md _ PRE NCP NCA)
| lia | exact VC1 | exact VC2 | exact VC3 | exact VC4 | exact VC5 | ].
intros W' c' FP. cbv beta. rewrite (Hk1 1 ltac:(discriminate)). cbn [ibind].
rewrite C1. replace (65536 <? Z.of_nat (length s)) with false by (symmetry; apply Z.ltb_ge; lia).
cbn [ibind YG00.ret]. rewrite RepAppPcf.st_setsize_eq. cbn [ibind snd].
apply HK.
destruct FP as (a & mat & matF & regs' & mem' & FP). cbv zeta in FP.
destruct FP as (Hwle & HwA & _ & HwH2 & Hgr' & Ha0 & Ha1 & -> & Hrp & FR & PRr & NBr & V0' & V16' & V32' & V40' & V48' & Hio & _).
exact (RepAppPcf.post_first B lk Hp ly S S1 W regs mem md s a mat matF regs' mem' W' _ _ eq_refl eq_refl
  H_pfa PRE REGS EM L65 ROOM (H_aledger lk Hp ly S W mem md PRE) WF1 Hfr Hsec
  Hwle HwA HwH2 Hgr' Ha0 Ha1 Hrp FR PRr NBr V0' V16' V32' V40' V48' Hio).
Qed.

Lemma pru_round : forall n, page_round_up_Z n = round_up n kPage.
Proof. intros n. reflexivity. Qed.

Theorem append_ok_w : RepIFcf.append_spec_cf B.
Proof.
unfold RepIFcf.append_spec_cf.
intros R Hp ly S W regs mem md p s lk K Q PRE ROOM REGS H10 Hp1 Hp2 HLEN HSTR HNUL HK.
destruct (errb_mapped_cf S) eqn:EM;
[| exact (app_case1 R Hp ly S W regs mem md p s lk K Q EM ltac:(unfold ERRB_INIT in HLEN; lia) PRE ROOM REGS H10 Hp1 Hp2 HSTR HNUL HK) ].
pose proof (RepAppcf.rep_pre_cells B lk Hp ly S W mem md PRE) as (C0 & C16 & C32 & C40 & C48 & CV & Csc & Cal).
rewrite EM in C0.
destruct (RepAppXcf.app_apart_of_pre B lk Hp ly S W mem md regs PRE REGS) as (Hhigh & Hstk & Hs0 & Hnob & Hc47 & Hd0 & Hdts & Hd64 & Hmap & Hbuf & Hgr & VK & VC1 & VC2 & VC3 & VC4 & VC5).
destruct (Hmap EM) as (Hcap0 & Hdpos & Hdal & Hdin). clear Hmap.
pose proof REGS as (_ & _ & Hra & _ & Hal & Hlo & Hhi & Hwin).
unfold APP_STK, spZ in *. unfold errb_room_for, kPage in ROOM. unfold kPage in Cal.
set (len := Z.of_nat (length s)) in *.
set (data := YG0ncf.errb_data_cf ly S) in *. set (cap := errb_cap_cf S) in *. set (size := errb_size_cf S) in *.
assert (HB : forall i, 0 <= i < cap -> apresent (w_H W) mem (data + i) /\ (data + i < TFIB_IMG_LO \/ TFIB_IMG_END <= data + i) /\
  (data + i < spZ regs - 512 \/ p + len + 1 <= data + i)).
{ intros i Hi. destruct (Hbuf i Hi) as [B1 B2]. split; [apply apresent_of_aview_off; [exact B1 | apply CV; lia]|].
  split; [unfold off_img in B1; lia | unfold spZ; lia]. }
unfold cfg_at, A_APPEND, w64.
destruct (cap <? size + len) eqn:EC.
- (* case 4: one remap *)
  apply Z.ltb_lt in EC.
  rewrite (RepAppcf.rep_append_mapped_grow len S EM ltac:(apply Z.ltb_lt; exact EC)).
  change (errb_size_cf S + Z.of_nat (length s)) with (size + len).
  destruct (RepAppcf.rep_map_ask (ci := ci) (errb_size_cf S + len) S) as (snap & S1 & k & Hask & Hk1 & Hfr & Hsec).
  rewrite Hask. cbn [ibind].
  pose proof PRE as (_ & _ & LY & IMG & TS & TSD & (_ & AR & _) & XM & WFP & QL & _ & _ & _ & HT).
  assert (Hlen0 : 0 < len) by lia.
  destruct (RepAppcf.rep_ncap_grow S len ltac:(lia) Hlen0 ROOM) as [NC1 _].
  pose proof AR as (_ & _ & _ & AMW & _).
  assert (NCP : 0 < page_round_up_Z (size + len)) by (pose proof (YK10.page_round_up_Z_ge (size + len)); lia).
  assert (NCA : page_round_up_Z (size + len) mod 4096 = 0) by exact (YK10.page_round_up_Z_aligned (size + len)).
  destruct (errb_map_fits_cf Hp ly S W _ md (page_round_up_Z (size + len)) LY IMG TS TSD AR XM QL HT NCP NCA
    ltac:(rewrite pru_round; exact NC1)) as [_ GB].
  subst len data cap size.
  eapply (app_grow _ Q snap (round_up (errb_size_cf S + Z.of_nat (length s)) kPage) W regs mem md p
    (YG0ncf.errb_data_cf ly S) (errb_cap_cf S) (errb_size_cf S) s);
  [ exact Hal | lia | intros a Ha; apply Hwin; lia | exact C0 | exact C16 | exact C32 | exact C40 | exact C48 | exact VK
  | exact H10 | exact Hp1 | lia | exact Hra | exact HSTR | exact HNUL | lia | lia | exact EC | lia | lia | lia | lia
  | exact HB | exact AMW
  | intros mat Hm; exact (RepAppcf.errb_map_not_refusable B errb_map_fits_cf Hp ly S W _ md mat _ LY IMG TS TSD AR XM QL HT NCP NCA
      ltac:(rewrite pru_round; exact NC1) Hm)
  | intros a Ha; destruct (Hgr a _ NCP NCA Ha) as [G1 G2]; split; [exact G1 | lia]
  | exact (H_glazy lk Hp ly S W mem md _ PRE NCP NCA)
  | lia | exact VC1 | exact VC2 | exact VC3 | exact VC4 | exact VC5
  | exact Hdal | exact Cal | exact Hdts | exact Hdin | exact Hdpos | ].
  intros W' c' RP. cbv beta. rewrite (Hk1 1 ltac:(discriminate)). cbn [ibind].
  rewrite RepAppPcf.st_setsize_eq. cbn [ibind snd].
  apply HK.
  assert (WF1 : WfP_cf (as_universe B) 0 (errb_slack S1) 0 S1)
    by exact (map_S1_wf (as_universe B) (errb_size_cf S + Z.of_nat (length s)) S snap S1 k WFP ltac:(lia) NC1 Hask Hk1).
  destruct RP as (a & mat & matF & regs' & mem' & RP). cbv zeta in RP.
  replace (errb_cap_cf S =? 0) with false in RP by (symmetry; apply Z.eqb_neq; lia).
  destruct RP as (Hwle & HwA & _ & HwH2 & Hgr' & Ha0 & Ha1 & -> & Hrp & FR & _ & PRr & NBr & V0' & V16' & V32' & V40' & V48' & Hio & _).
  exact (RepAppPcf.post_remap B lk Hp ly S S1 W regs mem md s a mat matF regs' mem' W' _ _ eq_refl eq_refl
    H_pfa PRE REGS EM ltac:(lia) EC ltac:(unfold errb_room_for, kPage in *; lia) ROOM (H_aledger lk Hp ly S W mem md PRE) WF1 Hfr Hsec
    Hwle HwA HwH2 Hgr' Ha0 Ha1 Hrp FR PRr NBr V0' V16' V32' V40' V48' Hio).
- (* case 3: room, no Realloc *)
  apply Z.ltb_ge in EC.
  rewrite (RepAppcf.rep_append_mapped_fit len S EM ltac:(apply Z.ltb_ge; exact EC)).
  rewrite RepAppPcf.st_setsize_eq. cbn [ibind snd].
  subst len data cap size.
  apply (amreal_SRr_pre tfibsegs _ _ _ _ (keep_post W regs mem md (YG0ncf.errb_data_cf ly S) (errb_cap_cf S) (errb_size_cf S) s)).
  + apply (app_keep W regs mem md p (YG0ncf.errb_data_cf ly S) (errb_cap_cf S) (errb_size_cf S) s); first [exact Hal | lia | exact C0 | exact C16 | exact C32 | exact C40 | exact C48
      | exact VK | exact H10 | exact Hp1 | exact Hra | exact HSTR | exact HNUL | exact HB | intros a Ha; apply Hwin; lia].
  + intros W' c' _ KP. destruct KP as (-> & regs' & mem' & mat & -> & RP & FR & PRS & V0 & V16 & V32 & V40 & V48 & _).
    apply HK. apply (RepAppPcf.post_keep B lk Hp ly S W regs mem md s regs' mem' mat H_pfa PRE REGS ROOM EM EC RP); assumption.
Qed.
End t.
