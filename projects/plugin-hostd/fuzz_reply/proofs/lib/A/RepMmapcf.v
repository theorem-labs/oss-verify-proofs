(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Copyright 2026 Theorem Labs *)
(* Modified by Theorem Labs, 2026-10: from proofs/cgif/cgif_file_fuzzer/lib/RepMmapcf.v (commit f01d79f3fb5, cf refill round 3; file sha256 125553fbc3b9) onto plugin-hostd/fuzz_reply's asan image (unstripped fuzz_reply.asan, sha256 d751b179ea49; pin 42c58610e125); module paths changed; its 39 image addresses moved by function pairs the comparison kit cmpkit 86da41d3ef68 calls the same code except at the by-hand acceptances named below (strictcmp3 65688e94214a, by funcpair_reply 6963bc4a94fc on the cgif twin ce511d541cda; 42 port_addr_check e55e1b52a8a0 MAPS predictions, each code one re-derived by the pair, each data one a pc-relative target of both paired functions; 0 code pcs the tool read as sizes, by the pair; 1 pair(s) carry a BY-HAND acceptance (accept.tsv, re-measured each run): _ZN11__sanitizer17GetNamedMappingFdEPKcmPi+0x90 (lui-in-section: CONSTANT)), and 16 pcs named in comments; 9 hand maps (resolve-run-f01d79f3fb5.tsv (sha256 ba54f3af32ab; internal record), each with its evidence: pinned image bytes, YImgTop, the unit AF twin); no other numeral changed. *)
(* Theorem Labs, 2026-10-30 (a Theorem Labs lane, F4 sub-slice MmapOrDieWalk): __sanitizer::MmapOrDie (0x670d4) of
   cgif_file_fuzzer's asan-ubsan image (pin 1c29845fe605), granted path, as the model's KMmapSec node.
   rule 24: proves function __sanitizer::MmapOrDie (reuse search: `proof-index VSNPrintf Printf
   SharedPrintfCode AppendNumber AppendToErrorMessageBuffer MmapOrDie` 2026-10-30T02:25:54Z, index v5 built
   2026-10-30T01:54:20Z: `MmapOrDie: 1 named, 106 by address, 2 related, 0 released lemma(s)`; rule-24 check
   RepLookupCheck CONFIRM: nothing reusable).

   The walk: the GetPageSize cache (the word at 0x9e1e8 holds 0x135d20, the word at 0x135d20 holds 4096), the page
   round-up of the size, the flags word 0x22 at sp+4, GetNamedMappingFd (0x67db0: a null name, or
   common_flags()->decorate_proc_maps, the byte at 0x137da8 + 0x104 = 0x137eac, is 0: returns -1), internal_mmap
   (0x65a04: a7 = 222, the ecall at 0x65a08, YF05.v:149 anon_node), internal_iserror (0x659e4) twice,
   IncreaseTotalMmap (0x618e8: mmap_limit_mb, the word at 0x137da8 + 0x90 = 0x137e38, is 0, so it returns before the
   amoadd.d at 0x61900; g_total_mmaped at 0x135d38 is not touched), and the return of the mapped address in a0.
   The common_flags() pointer is the word at 0x9e1f8 (0x137da8, YE37.v:31).  Every image cell the walk reads is a
   val_mem premise.

   Results: [mmapordie_node] (the model's IAsk (KMmapSec _) realized by the machine's mmap node, the caller's
   continuation K 1 at the return), [mmapordie_node_b] (the same, the continuation also told 0 <= a < 2 ^ 64),
   [mmapordie_granted] (the same walk as one entry-to-return SRr spec), and the
   premise builders [mmap_not_refusable_of_room] and [mmap_apart_of_layout].  The no-refusal premise quantifies
   only over the backings AI admits (length mat * page_size <= A_bytes); over every backing it would be false. *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.LinuxProcessSem.Sys.Mm Require Import Mmap.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s YO0d.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YP0j.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YN3v YI04.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YK04 YA0i YA0n YA0o YA0p YA0q.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0v YG0n YG0d.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import AB1v AB1q AB1t AF0l AF0m AF0x AFl0.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YO0a.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import AB1w AE3d AFeq AB13.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YE08.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import AB15 AFff.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YK0v YK13 YK02 YA09 YP0n YG0b YF05.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import AFgv.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable.Z Require Import Placement.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YM05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.
Set Printing Depth 100. Set Printing Width 200.

(* ---------------------------------------------------------------------------------------------------------------- *)
(* 1. The decode table and the symbolic states.                                                                      *)
(* MmapOrDie's 67 instructions (0x670d4 .. 0x671e0) on top of tfibtbl_rtC (YB1q.v:22), which covers the callees:
   0x618e8 (IncreaseTotalMmap), 0x659e4 (internal_iserror, internal_mmap), 0x67db0 (GetNamedMappingFd). *)
Definition tbl_mod_build : ctable := build_table tfibsegs 0x670d4 67%nat tfibtbl_rtC.
Definition tbl_mod : ctable := Eval vm_compute in tbl_mod_build.
Lemma tbl_mod_eq : tbl_mod = tbl_mod_build.
Proof. vm_cast_no_check (@eq_refl ctable tbl_mod). Qed.
Lemma tbl_mod_ok : table_ok tfibsegs tbl_mod.
Proof. rewrite tbl_mod_eq. unfold tbl_mod_build. apply build_table_ok; [cbv; discriminate|]. exact tfibtbl_rtC_ok. Qed.

(* The stack window below the entry sp: MmapOrDie's 0x30 frame (0x670d4) and GetNamedMappingFd's 0x110 frame
   (0x67db0); internal_mmap, internal_iserror and IncreaseTotalMmap's early-out path take no frame. *)
Definition MOD_STK : Z := 0x140.
Definition A_MOD : Z := 0x670d4.
Definition rSTKm : YP09.region := YP09.mkRegion (Some 2%nat) (- MOD_STK) 0 (- MOD_STK) 0 [].
Definition rFLP : YP09.region := flit8 0x9d9c0 0x137be8.  (* the common_flags() pointer *)
Definition rDPM : YP09.region := flit1 0x137cec 0.        (* common_flags()->decorate_proc_maps *)
Definition rMLM : YP09.region := flit8 0x137c78 0.        (* common_flags()->mmap_limit_mb *)
Definition IFM : facts := mkFacts [ (2%nat, mkAF (TFIB_IMG_END + MOD_STK) (2 ^ 64 - 1) 4); (10%nat, mkAF 1 (2 ^ 48 - 1) 0) ] [] [].
Definition SS_M : sstate := mkSS A_MOD sr_atoms [rSTKm; rPSP; rPS; rFLP; rDPM; rMLM] None IFM.
(* the state at GetNamedMappingFd's `beqz s2` (0x67dd8) on the name pointer *)
Definition SS_B : sstate := Eval vm_compute in fst (sym_run_toN_sh tfibsegs tbl_mod FUEL 0x65a08 SS_M).
(* the state at the ecall (0x65a08) on the null-name arm; the other arm reaches the same registers, regions, atoms *)
Definition SS_ET : sstate := Eval vm_compute in fst (sym_runN_sh tfibsegs tbl_mod FUEL (add_cond SS_B (mkAC BC_EQ (SOff 11 0) (SLit 0)))).
Definition REG_E := Eval vm_compute in ss_regs SS_ET.
Definition MEM_E := Eval vm_compute in ss_mem SS_ET.
Definition ATOMS_E := Eval vm_compute in f_atoms (ss_facts SS_ET).
(* the granted address: atom 32 *)
Definition GA : afact := mkAF 4096 (2 ^ 64 - 2 ^ 23 - 4096) 12.
Definition G_R : facts := mkFacts ((32%nat, GA) :: ATOMS_E) [] [].
Definition SS_R : sstate := mkSS 0x65a0c (sr_set REG_E 10 (SOff 32 0)) MEM_E None G_R.

(* ---------------------------------------------------------------------------------------------------------------- *)
(* 2. Arithmetic and model helpers.                                                                                  *)
Lemma pru_idem : forall x, x mod 4096 = 0 -> page_round_up_Z x = x.
Proof.
intros x Hx. unfold page_round_up_Z, page_size. apply Z.mod_divide in Hx as [q Hq]; [|lia]. subst x.
replace (q * 4096 + 4096 - 1) with (4095 + q * 4096) by lia. rewrite Z.div_add by lia. change (4095 / 4096) with 0. lia.
Qed.
Lemma pru_facts : forall sz, 0 < sz < 2 ^ 48 ->
4096 <= page_round_up_Z sz <= 2 ^ 48 /\ page_round_up_Z sz mod 4096 = 0 /\ sz <= page_round_up_Z sz.
Proof.
intros sz Hs. unfold page_round_up_Z, page_size. replace (sz + 4096 - 1) with (sz + 4095) by lia.
pose proof (Z.mul_div_le (sz + 4095) 4096 ltac:(lia)) as Q1. pose proof (Z.mul_succ_div_gt (sz + 4095) 4096 ltac:(lia)) as Q2.
split; [lia|]. split; [apply Z_mod_mult | lia].
Qed.
Lemma round_val : forall sz, 0 < sz < 2 ^ 48 ->
zcanon (zcanon (Z.land (zcanon (sz + 4095)) (zcanon 18446744073709547520)) + zcanon 0) = page_round_up_Z sz.
Proof.
intros sz Hs. unfold zcanon, M64.
rewrite (Z.mod_small (sz + 4095)) by lia. rewrite (Z.mod_small 18446744073709547520) by lia.
rewrite land_m4096 by lia. pose proof (Z.mod_pos_bound (sz + 4095) 4096 ltac:(lia)) as B.
rewrite (Z.mod_small (sz + 4095 - (sz + 4095) mod 4096)) by lia. rewrite Z.mod_0_l by lia. rewrite Z.add_0_r.
rewrite Z.mod_small by lia. unfold page_round_up_Z, page_size. replace (sz + 4096 - 1) with (sz + 4095) by lia.
rewrite (Z.mod_eq (sz + 4095) 4096) by lia. lia.
Qed.
Lemma A_bytes_page : forall A, A_wf A -> 0 <= A_bytes A /\ A_bytes A mod 4096 = 0.
Proof.
induction A as [|[lo hi] r IH]; intros HA; cbn [A_bytes fst snd]; [split; reflexivity|].
inversion HA as [|? ? Hiv Hr]; subst. destruct Hiv as (H1 & H2 & H3). cbn [fst snd] in H1, H2, H3.
destruct (IH Hr) as [IH1 IH2]. unfold page_size in H2, H3. split; [lia|].
rewrite Zplus_mod, Zminus_mod, H2, H3, IH2. reflexivity.
Qed.
Lemma grant_pin_parts : forall m (a : word) n, grant_ok_na_pin m a n = true ->
bv_unsigned a mod 4096 = 0 /\ 0 < bv_unsigned a /\ bv_unsigned a + n <= alloc_top (m_vmmaps m) /\
region_free (vm_reserved (m_vmmaps m) ++ vm_maps (m_vmmaps m)) a (Z_to_bv 64 n) = true.
Proof.
intros m a n Hg. unfold grant_ok_na_pin in Hg.
apply andb_prop in Hg as [Hg Hrf]. apply andb_prop in Hg as [Hg Htop]. apply andb_prop in Hg as [Hal Hpos].
apply Z.eqb_eq in Hal. apply Z.ltb_lt in Hpos. apply Z.leb_le in Htop. unfold page_size in Hal. repeat split; assumption.
Qed.
Lemma alloc_top_lt : forall h, alloc_top h <= 2 ^ 64 - 1 - 8388608.
Proof. intros h. unfold alloc_top, stack_max_size. pose proof (u64_range (vm_init_sp h)). lia. Qed.
Lemma lit_m1r : Z_to_bv 64 18446744073709551615 = Z_to_bv 64 (-1).
Proof. apply bv_eq. reflexivity. Qed.
Lemma model_after_grant : forall md (mat1 mat' : list word) (a n : word),
with_vm_backing (m_vm_lazy (with_mmap_backing (Z_to_bv 64 34) a n (mmap_model a n (with_vm_backing (m_vm_lazy md) mat1 md)))) mat'
  (with_mmap_backing (Z_to_bv 64 34) a n (mmap_model a n (with_vm_backing (m_vm_lazy md) mat1 md)))
= with_mmap_backing (Z_to_bv 64 34) a n (mmap_model a n (with_vm_backing (m_vm_lazy md) mat' md)).
Proof.
intros md mat1 mat' a n. unfold with_mmap_backing.
replace (mmap_noreserve_b (Z_to_bv 64 34)) with false by reflexivity.
destruct md as [fd [maps lazy mat] io fs proc lim tm]. reflexivity.
Qed.

(* ---------------------------------------------------------------------------------------------------------------- *)
(* 3. Symbolic-state helpers.                                                                                        *)
Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
(* a zero fill apart from every region keeps the regions *)
Lemma mem_ok_zfill_apart : forall E (H : word -> bool) mem rs (a n : word),
mem_ok tfibsegs E (mrestrict H mem) rs ->
(forall r, In r rs -> base_val E (YP09.r_base r) + YP09.r_hi r <= bv_unsigned a \/
  bv_unsigned a + bv_unsigned n <= base_val E (YP09.r_base r) + YP09.r_lo r) ->
mem_ok tfibsegs E (mrestrict H (zfill a n mem)) rs.
Proof.
intros E H mem rs a n (Hwf & Hok & Hpd) Hdis.
assert (GR : mem_grows (mrestrict H mem) (mrestrict H (zfill a n mem))).
{ intros x Hx. unfold mrestrict in *. destruct (H x); [exact Hx|]. unfold zfill. apply zmem_grows. exact Hx. }
split; [exact Hwf|]. split; [|exact Hpd].
rewrite Forall_forall in Hok |- *. intros r Hin.
destruct (Hok r Hin) as (H1 & H2 & H3 & H4). specialize (Hdis r Hin).
split; [exact H1|]. split; [exact H2|]. split.
- intros o Ho. eapply (writable_at_grows tfibsegs); [exact GR | apply H3; exact Ho].
- rewrite Forall_forall in H4 |- *. intros c Hc i Hi.
destruct (H4 c Hc i Hi) as (b & Hb1 & Hb2). exists b. split; [exact Hb1|].
assert (Hwfr : YP09.region_wf r = true) by (eapply regions_wf_In; eauto).
apply region_wf_facts in Hwfr as (_ & _ & Hci).
pose proof (chunk_inside_facts r c (proj1 (forallb_forall _ _) Hci c Hc)) as (Hc1 & Hc2 & Hc3).
rewrite (mbyte_mrestrict_same H mem (zfill a n mem)); [exact Hb2|].
apply zfill_out. rewrite unsigned_lit_small by lia. lia.
Qed.
(* a frame whose only writable window is the stack region [sp - MOD_STK, sp) *)
Lemma frame_stack : forall E rs (m m' : word -> option byte) sp (x : word),
frame_of E rs m m' ->
forallb (fun t => win_eqb t (Some 2%nat, - MOD_STK, 0) || (snd t <=? snd (fst t))) (windows rs) = true ->
bv_unsigned (ew E 2) = sp ->
~ (sp - MOD_STK <= bv_unsigned x < sp) -> m' x = m x.
Proof.
intros E rs m m' sp x HF Hb Hsp Hx. apply HF. intros Hin. apply Hx.
assert (X : sp + - MOD_STK <= bv_unsigned x < sp + 0) by (eapply in_wrange_single_b; eassumption). lia.
Qed.

(* ---------------------------------------------------------------------------------------------------------------- *)
(* 4. The KMmapSec node body (YG0d.v:72-84, q = KMmapSec).                                                          *)
Definition mmap_node_post {R : Type} (snap : astate) (ncap : Z) (K : Z -> itree astate R)
  (Q : R -> world tfibsegs -> config -> Prop) : world tfibsegs -> config -> Prop :=
fun W1 c1 => exists (I : Type) (nx : I -> config) (bit : I -> Z) (sp : I -> bool) (i0 : I),
  node_ok tfibsegs c1 I (fun _ => []) nx /\
  (forall i, AI tfibsegs (w_H W1) (w_A W1) (cfg_model c1) -> AI tfibsegs (w_H W1) (w_A W1) (cfg_model (nx i))) /\
  (forall i, aok snap (KMmapSec ncap) (bit i)) /\ sp i0 = false /\ bit i0 = 1 /\
  (forall i, sp i = false -> bit i = 1) /\
  (forall i, sp i = true -> AI tfibsegs (w_H W1) (w_A W1) (cfg_model (nx i)) -> srealizes tfibsegs (nx i) t_nil) /\
  (forall i, sp i = false -> amreal tfibsegs (K (bit i)) W1 (nx i) Q).
Lemma amreal_mmap_ask : forall {R : Type} (snap : astate) (ncap : Z) (K : Z -> itree astate R) W c Q,
SRr tfibsegs W c (mmap_node_post snap ncap K Q) -> amreal tfibsegs (IAsk (KMmapSec ncap) snap K) W c Q.
Proof. intros R snap ncap K W c Q H. exact H. Qed.

(* the caller's continuation, after the grant at [a] *)
Definition mod_cont {R : Type} (K : Z -> itree astate R) (Q : R -> world tfibsegs -> config -> Prop)
  (W : world tfibsegs) (regs : bvmap 5 word) (mem : word -> option byte) (md : Model) (sz : Z) : Prop :=
let H := w_H W in let sp := bv_unsigned (getr regs 2) in let nZ := page_round_up_Z sz in
forall (a : Z) (regs' : bvmap 5 word) (mem' : word -> option byte) (mat : list word),
  let mdN := with_vm_backing (m_vm_lazy md) mat md in
  let md1 := with_mmap_backing (w64 34) (w64 a) (w64 nZ) (mmap_model (w64 a) (w64 nZ) mdN) in
  0 <= a < 2 ^ 64 -> grant_ok_na_pin mdN (w64 a) nZ = true ->
  regs_preserved regs regs' -> getr regs' 10 = w64 a ->
  (forall x : word, ~ (sp - MOD_STK <= bv_unsigned x < sp) -> ~ (a <= bv_unsigned x < a + nZ) -> mem' x = mem x) ->
  (forall x : word, a <= bv_unsigned x < a + nZ -> mem' x = Some (Z_to_bv 8 0)) ->
  (forall b, apresent H mem b -> apresent H mem' b) ->
  YG0d.same_io md md1 ->
  amreal tfibsegs (K 1) W (mkCfg (mkst regs' (getr regs 1) mem' (seg_rom tfibsegs)) md1) Q.

(* ---------------------------------------------------------------------------------------------------------------- *)
(* 5. From the ecall to the return.                                                                                  *)
Lemma mod_at_ecall : forall {R : Type} (K : Z -> itree astate R) (Q : R -> world tfibsegs -> config -> Prop)
  (snap : astate) (ncap : Z) (W : world tfibsegs) (regs : bvmap 5 word) (mem : word -> option byte) (md : Model)
  (sz : Z) (ss : sstate) (ms : machine_state) (mat : list word),
let sp := bv_unsigned (getr regs 2) in let nZ := page_round_up_Z sz in
getr regs 10 = w64 sz -> YK0s.ret_ok (getr regs 1) -> 0 < sz -> sz < 2 ^ 48 -> MWF md ->
(forall mat, Z.of_nat (length mat) * page_size <= A_bytes (w_A W) ->
   mmap_grant_refusable (w64 34) (with_vm_backing (m_vm_lazy md) mat md) nZ = false) ->
(forall a : word, grant_ok_na_pin md a nZ = true ->
   (bv_unsigned a + nZ <= sp - MOD_STK \/ sp <= bv_unsigned a) /\ (bv_unsigned a + nZ <= 0x9d000 \/ 0x5fb000 <= bv_unsigned a)) ->
TFIB_IMG_END <= sp - MOD_STK ->
mod_cont K Q W regs mem md sz ->
st_ok_ecall tfibsegs (Ereg regs []) ss (restrict (w_H W) ms) ->
ss_pc ss = 0x65a08 -> ss_regs ss = REG_E -> ss_mem ss = MEM_E -> ss_resv ss = None -> f_atoms (ss_facts ss) = ATOMS_E ->
(forall x : word, ~ (sp - MOD_STK <= bv_unsigned x < sp) -> ms_mem ms x = mem x) ->
SRr tfibsegs W (mkCfg ms (with_vm_backing (m_vm_lazy md) mat md)) (mmap_node_post snap ncap K Q).
Proof.
intros R K Q snap ncap W regs mem md sz ss ms mat. cbv zeta.
intros H10 Hra Hsz0 Hsz1 HMWF HGR HAP Hsp HK HS Hpc Hrg Hmm Hrv Hat FRe.
pose proof Hwx_tfa as Hwx.
pose proof (u64_range (getr regs 2)) as Usp. set (sp := bv_unsigned (getr regs 2)) in *.
pose proof (pru_facts sz (conj Hsz0 Hsz1)) as (NZ1 & NZ2 & NZ3).
set (nZ := page_round_up_Z sz) in *.
set (E0 := Ereg regs []) in *.
assert (E2 : ew E0 2 = getr regs 2) by (exact (ew_Ereg_nat regs [] 2 2%bv eq_refl)).
assert (E1 : ew E0 1 = getr regs 1) by (exact (ew_Ereg_nat regs [] 1 1%bv eq_refl)).
assert (E10 : ew E0 10 = getr regs 10) by (exact (ew_Ereg_nat regs [] 10 10%bv eq_refl)).
destruct (st_ok_ecall_shape_r tfibsegs (w_H W) E0 ss ms HS Hrv) as (regsE & memE & Hms & Hregs & Hmem & HG).
rewrite Hpc in Hms. subst ms. clear HS.
cbn [ms_mem pend_at] in FRe.
assert (HAt : atoms_ok E0 ATOMS_E) by (rewrite <- Hat; exact (proj1 HG)). clear HG.
assert (HregsE : regs_ok E0 REG_E regsE) by (rewrite <- Hrg; exact Hregs).
assert (HmemE : mem_ok tfibsegs E0 (mrestrict (w_H W) memE) MEM_E) by (rewrite <- Hmm; exact Hmem). clear Hmem.
(* the registers of the ecall *)
assert (R17 : getr regsE 17 = Z_to_bv 64 222) by (rewrite (HregsE 17%bv); reflexivity).
assert (R10 : getr regsE 10 = Z_to_bv 64 0) by (rewrite (HregsE 10%bv); reflexivity).
assert (R12 : getr regsE 12 = Z_to_bv 64 3) by (rewrite (HregsE 12%bv); reflexivity).
assert (R13 : getr regsE 13 = Z_to_bv 64 34) by (rewrite (HregsE 13%bv); reflexivity).
assert (R15 : getr regsE 15 = Z_to_bv 64 0) by (rewrite (HregsE 15%bv); reflexivity).
assert (R14 : getr regsE 14 = Z_to_bv 64 (-1)) by (rewrite (HregsE 14%bv); exact lit_m1r).
assert (R11 : getr regsE 11 = Z_to_bv 64 nZ).
{ rewrite (HregsE 11%bv).
  assert (S11 : sr_get REG_E 11%bv = SAlu ALU_ADD (SAlu ALU_AND (SOff 10 4095) (SLit 18446744073709547520)) (SLit 0)) by (vm_compute; reflexivity).
  rewrite S11. rewrite <- (Z_to_bv_bv_unsigned 64 (sv_denot E0 _)). f_equal.
  change (bv_unsigned (sv_denot E0 (SAlu ALU_ADD (SAlu ALU_AND (SOff 10 4095) (SLit 18446744073709547520)) (SLit 0))))
    with (U E0 (SAlu ALU_ADD (SAlu ALU_AND (SOff 10 4095) (SLit 18446744073709547520)) (SLit 0))).
  rewrite (U_zev E0 (SAlu ALU_ADD (SAlu ALU_AND (SOff 10 4095) (SLit 18446744073709547520)) (SLit 0)) eq_refl).
  cbn [zev zalu_raw]. unfold rho_of. rewrite E10, H10. unfold w64.
  rewrite unsigned_lit_small by lia. exact (round_val sz (conj Hsz0 Hsz1)). }
(* the grant at the node *)
apply (SRr_use_AI tfibsegs). intros HAI. cbn [cfg_model] in HAI.
pose proof (mat_le_A tfibsegs (w_H W) (w_A W) _ HAI) as HMA. rewrite m_vm_materialized_wvb in HMA.
pose proof (HGR mat HMA) as HRF.
pose proof HRF as HRF'. unfold mmap_grant_refusable in HRF'. apply orb_false_iff in HRF' as [HB _]. apply negb_false_iff in HB.
destruct (grant_of_not_refusable (Z_to_bv 64 0) _ nZ HRF) as [a0 Ha0].
pose proof (grant_ok_na_pin_of_grant_ok _ _ _ _ Ha0) as Ha0'.
assert (MWFN : MWF (with_vm_backing (m_vm_lazy md) mat md)) by (eapply MWF_same_but_materialized; [exact HMWF | reflexivity]).
assert (SLK : eager_used (with_vm_backing (m_vm_lazy md) mat md) + A_bytes (w_A W) + nZ <= vm_limit (m_vmmaps (with_vm_backing (m_vm_lazy md) mat md))).
{ destruct (A_bytes_page (w_A W) (w_Awf W)) as [AB0 AB1].
  pose proof (Z.div_mod (A_bytes (w_A W)) 4096 ltac:(lia)) as AB2. rewrite AB1, Z.add_0_r in AB2.
  assert (AB3 : 0 <= A_bytes (w_A W) / 4096) by (apply Z.div_pos; lia).
  assert (LEN : Z.of_nat (length (repeat (Z_to_bv 64 0) (Z.to_nat (A_bytes (w_A W) / 4096)))) * page_size <= A_bytes (w_A W)).
  { rewrite repeat_length, Z2Nat.id by lia. unfold page_size. lia. }
  pose proof (HGR _ LEN) as X. unfold mmap_grant_refusable in X. apply orb_false_iff in X as [X _]. apply negb_false_iff in X.
  unfold mmap_noreserve_backed_ok in X. change (mmap_noreserve_b (w64 34)) with false in X. cbv iota in X. apply Z.leb_le in X.
  rewrite vm_backing_used_split, eager_used_wvb, m_vm_materialized_wvb, m_vmmaps_wvb in X.
  rewrite repeat_length, Z2Nat.id in X by lia. rewrite eager_used_wvb, m_vmmaps_wvb. unfold page_size in X. lia. }
destruct (anon_node tfibsegs regsE (Z_to_bv 64 0x65a08) memE (seg_rom tfibsegs) (with_vm_backing (m_vm_lazy md) mat md) (Z_to_bv 64 34) nZ
  (AI_halted _ _ _ _ HAI) R17 R10 R11 ltac:(lia) R12 R13 eq_refl R14 R15
  ltac:(rewrite (pru_idem nZ NZ2); exists a0; exact Ha0') ltac:(rewrite (pru_idem nZ NZ2); exact HB))
  as (Ix & nx & bit & ga & i0 & NODE & _ & OUT).
rewrite (pru_idem nZ NZ2) in OUT.
apply (SRr_ret tfibsegs). unfold mmap_node_post.
exists Ix, nx, (fun _ => 1), (fun _ => false), i0.
split; [exact NODE|].
split.
{ intros i _. destruct (OUT i) as (md_i & _ & _ & _ & Hg & -> & ->). cbn [cfg_model].
  destruct (grant_pin_parts _ _ _ Hg) as (G1 & G2 & G3 & G4).
  pose proof (commit_AI tfibsegs (w_H W) (w_A W) (with_vm_backing (m_vm_lazy md) mat md) true (Z_to_bv 64 34) (ga i) nZ HAI MWFN
    eq_refl ltac:(unfold page_size; exact G1) ltac:(lia) ltac:(rewrite (pru_idem nZ NZ2); exact G3)
    ltac:(cbv iota; rewrite (pru_idem nZ NZ2); exact G4) ltac:(rewrite (pru_idem nZ NZ2); exact SLK)) as CA.
  cbv zeta in CA. rewrite (pru_idem nZ NZ2) in CA. exact (proj1 (proj1 CA)). }
split; [intros i; cbn [aok]; right; reflexivity|].
split; [reflexivity|]. split; [reflexivity|]. split; [intros; reflexivity|].
split; [intros i Hi; discriminate Hi|].
intros i _. cbv beta.
destruct (OUT i) as (md_i & _ & IO_i & _ & Hg & NX & MD). rewrite NX. subst md_i. clear NX OUT NODE.
destruct (grant_pin_parts _ _ _ Hg) as (G1 & G2 & G3 & G4).
pose proof (alloc_top_lt (m_vmmaps md)) as ATL. rewrite m_vmmaps_wvb in G3.
assert (GAr : 4096 <= bv_unsigned (ga i) <= 2 ^ 64 - 2 ^ 23 - 4096).
{ clear - G1 G2 G3 ATL NZ1. apply Z.mod_divide in G1 as [q Hq]; [|lia]. rewrite Hq in *. lia. }
destruct (HAP (ga i) Hg) as (HAPs & HAPi).
pose proof (u64_range (ga i)) as Rga.
set (A := bv_unsigned (ga i)) in *.
assert (Ga : w64 A = ga i) by (unfold A, w64; apply Z_to_bv_bv_unsigned).
assert (UnZ : bv_unsigned (Z_to_bv 64 nZ) = nZ) by (apply unsigned_lit_small; lia).
(* the post-node walk *)
apply (amreal_SRr_pre tfibsegs (K 1) W _ Q
  (fun W' c' => W' = W /\ exists regs' mem' mat0,
     let mdN0 := with_vm_backing (m_vm_lazy md) mat0 md in
     let md1 := with_mmap_backing (w64 34) (w64 A) (w64 nZ) (mmap_model (w64 A) (w64 nZ) mdN0) in
     grant_ok_na_pin mdN0 (w64 A) nZ = true /\
     c' = mkCfg (mkst regs' (getr regs 1) mem' (seg_rom tfibsegs)) md1 /\
     regs_preserved regs regs' /\ getr regs' 10 = w64 A /\
     (forall x : word, ~ (sp - MOD_STK <= bv_unsigned x < sp) -> ~ (A <= bv_unsigned x < A + nZ) -> mem' x = mem x) /\
     (forall x : word, A <= bv_unsigned x < A + nZ -> mem' x = Some (Z_to_bv 8 0)) /\
     (forall b, apresent (w_H W) mem b -> apresent (w_H W) mem' b) /\
     YG0d.same_io md md1)).
2:{ intros W' c' _ [-> (regs' & mem' & mat0 & P0 & -> & P1 & P2 & P3 & P4 & P5 & P6)].
    exact (HK A regs' mem' mat0 Rga P0 P1 P2 P3 P4 P5 P6). }
assert (HS2 : st_ok tfibsegs (ewset E0 32 (ga i)) SS_R
  (restrict (w_H W) (mkst (regupd regsE 10 (ga i)) (v_addi (Z_to_bv 64 0x65a08) 4) (zfill (ga i) (Z_to_bv 64 nZ) memE) (seg_rom tfibsegs)))).
{ rewrite restrict_mkst_fx.
  replace SS_R with (resume ss (SOff 32 0) MEM_E G_R) by (unfold resume; rewrite Hpc, Hrg; reflexivity).
  apply (st_ok_resume tfibsegs E0 (ewset E0 32 (ga i)) 32 ss regsE (Z_to_bv 64 0x65a08)).
  - exact Hregs.
  - rewrite Hpc. reflexivity.
  - apply env_agree_ewset.
  - rewrite Hrg. vm_compute. reflexivity.
  - cbn [sv_denot]. rewrite ew_ewset_same, Z.add_0_r. apply Z_to_bv_bv_unsigned.
  - apply (mem_ok_agree tfibsegs 32 E0); [apply env_agree_ewset | vm_compute; reflexivity |].
    apply mem_ok_zfill_apart; [exact HmemE|].
    intros r Hr. unfold MEM_E in Hr. cbn [In] in Hr. rewrite UnZ. fold A.
    repeat (destruct Hr as [<-|Hr]; [cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val]; try rewrite E2; fold sp; unfold MOD_STK in *; lia|]).
    destruct Hr.
  - unfold G_R. split; [|split; exact I]. cbn [f_atoms atoms_ok]. split.
    + unfold afact_ok, GA. cbn [af_lo af_hi af_al2]. rewrite ew_ewset_same. fold A.
      split; [exact GAr|]. split; [change (2 ^ 12) with 4096; exact G1 | lia].
    + exact (proj1 (facts_ok_agree 32 E0 (ewset E0 32 (ga i)) (mkFacts ATOMS_E [] []) (env_agree_ewset E0 32 _)
        ltac:(vm_compute; reflexivity) (conj HAt (conj I I)))). }
srr_run_to_sh tbl_mod_ok HS2 0x671b0.
rename HF into HF3. clear HFr.
lazymatch type of HS2 with st_ok _ _ _ (restrict _ ?msx) => rename msx into ms3 end.
assert (BV2 : bv_unsigned (ew (ewset E0 32 (ga i)) 2) = sp) by (rewrite ew_ewset_other by lia; rewrite E2; reflexivity).
assert (FR3 : forall x : word, ~ (sp - MOD_STK <= bv_unsigned x < sp) -> ms_mem ms3 x = zfill (ga i) (Z_to_bv 64 nZ) memE x).
{ intros x Hx. exact (frame_stack _ _ _ _ sp x HF3 ltac:(vm_compute; reflexivity) BV2 Hx). }
clear HF3.
eapply (SRr_ret_at tfibsegs tbl_mod tbl_mod_ok Hwx W (ewset E0 32 (ga i))); [exact HS2 | reflexivity | vm_compute; reflexivity |].
intros mat'. split; [reflexivity|].
rreg HS2 (1%bv : bv 5) Q1. rreg HS2 (10%bv : bv 5) Q10.
exists (ms_regs ms3), (ms_mem ms3), mat'. cbv zeta.
rewrite Ga.
split; [exact Hg|].
split.
{ rewrite Q1, E1. unfold YK0s.ret_ok in Hra. rewrite Hra. rewrite wvb_collapse. unfold w64. rewrite (model_after_grant md mat mat'). reflexivity. }
split.
{ apply (regs_preserved_of_st_ok tfibsegs (ewset E0 32 (ga i)) _ _ regs [] HS2); [apply env_agree_ewset | vm_compute; reflexivity]. }
split. { rewrite Q10. reflexivity. }
split.
{ intros x Hx Hy. rewrite (FR3 x Hx). rewrite zfill_out by (rewrite UnZ; fold A; lia). exact (FRe x Hx). }
split.
{ intros x Hx. rewrite (FR3 x) by (clear - Hx HAPs; lia). apply zfill_in. rewrite UnZ. fold A. lia. }
split.
{ intros b Hb. pose proof (u64_range (Z_to_bv 64 b)) as Rx. set (x := Z_to_bv 64 b) in *.
  assert (Ex : Z_to_bv 64 (bv_unsigned x) = x) by apply Z_to_bv_bv_unsigned.
  destruct (Z_lt_le_dec (bv_unsigned x) (sp - MOD_STK)) as [L1|L1]; [|destruct (Z_lt_le_dec (bv_unsigned x) sp) as [L2|L2]].
  - destruct (Z_lt_le_dec (bv_unsigned x) A) as [L3|L3]; [|destruct (Z_lt_le_dec (bv_unsigned x) (A + nZ)) as [L4|L4]].
    + destruct Hb as [Hh [v Hv]]. split; [exact Hh|]. exists v. fold x in Hv |- *. rewrite (FR3 x) by lia. rewrite zfill_out by (rewrite UnZ; fold A; lia). rewrite (FRe x) by lia. exact Hv.
    + destruct Hb as [Hh _]. split; [exact Hh|]. exists (Z_to_bv 8 0). fold x. rewrite (FR3 x) by (clear - L4 L3 HAPs; lia). apply zfill_in. rewrite UnZ. fold A. lia.
    + destruct Hb as [Hh [v Hv]]. split; [exact Hh|]. exists v. fold x in Hv |- *. rewrite (FR3 x) by lia. rewrite zfill_out by (rewrite UnZ; fold A; lia). rewrite (FRe x) by lia. exact Hv.
  - pose proof (st_ok_window_apresent (w_H W) (ewset E0 32 (ga i)) _ _ 0%nat _ (bv_unsigned x) HS2 eq_refl
      ltac:(cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val]; rewrite BV2; unfold MOD_STK in *; lia)
      ltac:(unfold MOD_STK, TFIB_IMG_END in *; lia)) as AP.
    unfold apresent in AP |- *. rewrite Ex in AP. exact AP.
  - destruct (Z_lt_le_dec (bv_unsigned x) A) as [L3|L3]; [|destruct (Z_lt_le_dec (bv_unsigned x) (A + nZ)) as [L4|L4]].
    + destruct Hb as [Hh [v Hv]]. split; [exact Hh|]. exists v. fold x in Hv |- *. rewrite (FR3 x) by lia. rewrite zfill_out by (rewrite UnZ; fold A; lia). rewrite (FRe x) by lia. exact Hv.
    + destruct Hb as [Hh _]. split; [exact Hh|]. exists (Z_to_bv 8 0). fold x. rewrite (FR3 x) by (clear - L4 L3 L2 HAPs; lia). apply zfill_in. rewrite UnZ. fold A. lia.
    + destruct Hb as [Hh [v Hv]]. split; [exact Hh|]. exists v. fold x in Hv |- *. rewrite (FR3 x) by lia. rewrite zfill_out by (rewrite UnZ; fold A; lia). rewrite (FRe x) by lia. exact Hv. }
{ unfold w64. eapply same_io_trans; [apply same_io_with_vm_backing|].
  eapply same_io_trans; [apply same_io_with_vmmaps | apply same_io_with_mmap_backing]. }
Qed.

(* ---------------------------------------------------------------------------------------------------------------- *)
(* 6. MmapOrDie as the model's KMmapSec node (granted path, no refusal).                                            *)
Local Ltac reg_intro := unfold region_ok; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
(* the node with the granted address's range handed to the continuation *)
Lemma mmapordie_node_b : forall {R : Type} (K : Z -> itree astate R) (Q : R -> world tfibsegs -> config -> Prop)
  (snap : astate) (ncap : Z) (W : world tfibsegs) (regs : bvmap 5 word) (mem : word -> option byte) (md : Model) (sz : Z),
let H := w_H W in let m := mrestrict H mem in let sp := bv_unsigned (getr regs 2) in
let nZ := page_round_up_Z sz in
getr regs 10 = w64 sz -> YK0s.ret_ok (getr regs 1) -> 0 < sz -> sz < 2 ^ 48 ->
val_mem tfibsegs m 0x9d9b0 8 0x135b60 -> val_mem tfibsegs m 0x135b60 8 4096 ->
val_mem tfibsegs m 0x9d9c0 8 0x137be8 -> val_mem tfibsegs m 0x137cec 1 0 -> val_mem tfibsegs m 0x137c78 8 0 ->
MWF md ->
(forall mat, Z.of_nat (length mat) * page_size <= A_bytes (w_A W) ->
   mmap_grant_refusable (w64 34) (with_vm_backing (m_vm_lazy md) mat md) nZ = false) ->
(forall a : word, grant_ok_na_pin md a nZ = true ->
   (bv_unsigned a + nZ <= sp - MOD_STK \/ sp <= bv_unsigned a) /\ (bv_unsigned a + nZ <= 0x9d000 \/ 0x5fb000 <= bv_unsigned a)) ->
sp mod 16 = 0 -> TFIB_IMG_END <= sp - MOD_STK -> (forall b, sp - MOD_STK <= b < sp -> apresent H mem b) ->
(forall (a : Z) (regs' : bvmap 5 word) (mem' : word -> option byte) (mat : list word),
   let mdN := with_vm_backing (m_vm_lazy md) mat md in
   let md1 := with_mmap_backing (w64 34) (w64 a) (w64 nZ) (mmap_model (w64 a) (w64 nZ) mdN) in
   0 <= a < 2 ^ 64 -> grant_ok_na_pin mdN (w64 a) nZ = true ->
   regs_preserved regs regs' -> getr regs' 10 = w64 a ->
   (forall x : word, ~ (sp - MOD_STK <= bv_unsigned x < sp) -> ~ (a <= bv_unsigned x < a + nZ) -> mem' x = mem x) ->
   (forall x : word, a <= bv_unsigned x < a + nZ -> mem' x = Some (Z_to_bv 8 0)) ->
   (forall b, apresent H mem b -> apresent H mem' b) ->
   YG0d.same_io md md1 ->
   amreal tfibsegs (K 1) W (mkCfg (mkst regs' (getr regs 1) mem' (seg_rom tfibsegs)) md1) Q) ->
amreal tfibsegs (IAsk (KMmapSec ncap) snap K) W (mkCfg (mkst regs (w64 0x670d4) mem (seg_rom tfibsegs)) md) Q.
Proof.
intros R K Q snap ncap W regs mem md sz. cbv zeta.
intros H10 Hra Hsz0 Hsz1 HPSP HPS HFLP HDPM HMLM HMWF HGR HAP Hal Hsp HPRES HK.
apply amreal_mmap_ask.
pose proof Hwx_tfa as Hwx.
pose proof (u64_range (getr regs 2)) as Usp. set (sp := bv_unsigned (getr regs 2)) in *.
set (E0 := Ereg regs []).
assert (E2 : ew E0 2 = getr regs 2) by (exact (ew_Ereg_nat regs [] 2 2%bv eq_refl)).
assert (E10 : ew E0 10 = getr regs 10) by (exact (ew_Ereg_nat regs [] 10 10%bv eq_refl)).
assert (HS : st_ok tfibsegs E0 SS_M (restrict (w_H W) (mkst regs (Z_to_bv 64 A_MOD) mem (seg_rom tfibsegs)))).
{ unfold SS_M. rewrite restrict_mkst_fx. apply (entry_st_ok_full tfibsegs).
- apply regs_ok_Ereg.
- vm_compute. reflexivity.
- cbn [ms_mem mkst]. unfold rSTKm, rPSP, rPS, rFLP, rDPM, rMLM, flit8, flit1.
  apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]]]]]].
  + apply (region_ok_stack tfibsegs E0 _ 2 sp (- MOD_STK)); [rewrite E2; reflexivity | unfold MOD_STK, TFIB_IMG_END in *; lia | lia |].
    intros a Ha. apply apresent_writable; [unfold MOD_STK, TFIB_IMG_END in *; lia | apply HPRES; exact Ha].
  + reg_intro. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
    apply Forall_cons; [|apply Forall_nil]. eapply chunk_ok_val; [reflexivity | cbn; lia | cbn; lia | rewrite Z.add_0_l; exact HPSP].
  + reg_intro. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
    apply Forall_cons; [|apply Forall_nil]. eapply chunk_ok_val; [reflexivity | cbn; lia | cbn; lia | rewrite Z.add_0_l; exact HPS].
  + reg_intro. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
    apply Forall_cons; [|apply Forall_nil]. eapply chunk_ok_val; [reflexivity | cbn; lia | cbn; lia | rewrite Z.add_0_l; exact HFLP].
  + reg_intro. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
    apply Forall_cons; [|apply Forall_nil]. eapply chunk_ok_val; [reflexivity | cbn; lia | cbn; lia | rewrite Z.add_0_l; exact HDPM].
  + reg_intro. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
    apply Forall_cons; [|apply Forall_nil]. eapply chunk_ok_val; [reflexivity | cbn; lia | cbn; lia | rewrite Z.add_0_l; exact HMLM].
- apply pairwise_disjoint_of_extents. unfold rSTKm, rPSP, rPS, rFLP, rDPM, rMLM, flit8, flit1, extent_of_region.
  cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite (ew_Ereg_nat regs [] 2 2%bv eq_refl). fold sp.
  cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd]. unfold MOD_STK, TFIB_IMG_END in *. repeat split; lia.
- split; [|split; exact I]. cbn [IFM f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
  rewrite (ew_Ereg_nat regs [] 2 2%bv eq_refl), (ew_Ereg_nat regs [] 10 10%bv eq_refl), H10. fold sp. unfold w64. rewrite unsigned_lit_small by lia.
  unfold MOD_STK, TFIB_IMG_END in *.
  repeat split; first [lia | change (2 ^ 4) with 16; exact Hal | change (2 ^ 0) with 1; apply Z.mod_1_r]. }
change (w64 0x670d4) with (Z_to_bv 64 A_MOD).
srr_run_to_sh tbl_mod_ok HS 0x65a08.
rename HF into HF1. clear HFr.
lazymatch type of HS with st_ok _ _ _ (restrict _ ?msx) => rename msx into ms1 end.
assert (FR1 : forall x : word, ~ (sp - MOD_STK <= bv_unsigned x < sp) -> ms_mem ms1 x = mem x).
{ intros x Hx. exact (frame_stack E0 _ _ _ sp x HF1 ltac:(vm_compute; reflexivity) ltac:(rewrite E2; reflexivity) Hx). }
clear HF1.
srr_branch_sh tbl_mod_ok HS.
all: srr_run_sh tbl_mod_ok HS.
all: lazymatch type of HS with st_ok_ecall _ _ _ (restrict _ ?msx) => rename msx into ms2 end.
all: (apply (mod_at_ecall K Q snap ncap W regs mem md sz _ ms2 _ H10 Hra Hsz0 Hsz1 HMWF HGR HAP Hsp HK HS);
  [reflexivity | reflexivity | reflexivity | reflexivity | reflexivity |
   intros x Hx; rewrite (frame_stack E0 _ _ _ sp x HF ltac:(vm_compute; reflexivity) ltac:(rewrite E2; reflexivity) Hx); exact (FR1 x Hx)]).
Qed.
(* the node, as RepF4Append consumes it (merged at 3020f6582da) *)
Lemma mmapordie_node : forall {R : Type} (K : Z -> itree astate R) (Q : R -> world tfibsegs -> config -> Prop)
  (snap : astate) (ncap : Z) (W : world tfibsegs) (regs : bvmap 5 word) (mem : word -> option byte) (md : Model) (sz : Z),
let H := w_H W in let m := mrestrict H mem in let sp := bv_unsigned (getr regs 2) in
let nZ := page_round_up_Z sz in
getr regs 10 = w64 sz -> YK0s.ret_ok (getr regs 1) -> 0 < sz -> sz < 2 ^ 48 ->
val_mem tfibsegs m 0x9d9b0 8 0x135b60 -> val_mem tfibsegs m 0x135b60 8 4096 ->
val_mem tfibsegs m 0x9d9c0 8 0x137be8 -> val_mem tfibsegs m 0x137cec 1 0 -> val_mem tfibsegs m 0x137c78 8 0 ->
MWF md ->
(forall mat, Z.of_nat (length mat) * page_size <= A_bytes (w_A W) ->
   mmap_grant_refusable (w64 34) (with_vm_backing (m_vm_lazy md) mat md) nZ = false) ->
(forall a : word, grant_ok_na_pin md a nZ = true ->
   (bv_unsigned a + nZ <= sp - MOD_STK \/ sp <= bv_unsigned a) /\ (bv_unsigned a + nZ <= 0x9d000 \/ 0x5fb000 <= bv_unsigned a)) ->
sp mod 16 = 0 -> TFIB_IMG_END <= sp - MOD_STK -> (forall b, sp - MOD_STK <= b < sp -> apresent H mem b) ->
(forall (a : Z) (regs' : bvmap 5 word) (mem' : word -> option byte) (mat : list word),
   let mdN := with_vm_backing (m_vm_lazy md) mat md in
   let md1 := with_mmap_backing (w64 34) (w64 a) (w64 nZ) (mmap_model (w64 a) (w64 nZ) mdN) in
   grant_ok_na_pin mdN (w64 a) nZ = true ->
   regs_preserved regs regs' -> getr regs' 10 = w64 a ->
   (forall x : word, ~ (sp - MOD_STK <= bv_unsigned x < sp) -> ~ (a <= bv_unsigned x < a + nZ) -> mem' x = mem x) ->
   (forall x : word, a <= bv_unsigned x < a + nZ -> mem' x = Some (Z_to_bv 8 0)) ->
   (forall b, apresent H mem b -> apresent H mem' b) ->
   YG0d.same_io md md1 ->
   amreal tfibsegs (K 1) W (mkCfg (mkst regs' (getr regs 1) mem' (seg_rom tfibsegs)) md1) Q) ->
amreal tfibsegs (IAsk (KMmapSec ncap) snap K) W (mkCfg (mkst regs (w64 0x670d4) mem (seg_rom tfibsegs)) md) Q.
Proof.
intros R K Q snap ncap W regs mem md sz. cbv zeta.
intros H10 Hra Hsz0 Hsz1 HPSP HPS HFLP HDPM HMLM HMWF HGR HAP Hal Hsp HPRES HK.
apply (mmapordie_node_b K Q snap ncap W regs mem md sz H10 Hra Hsz0 Hsz1 HPSP HPS HFLP HDPM HMLM HMWF HGR HAP Hal Hsp HPRES).
intros a regs' mem' mat. cbv zeta. intros _. exact (HK a regs' mem' mat).
Qed.

(* ---------------------------------------------------------------------------------------------------------------- *)
(* 7. The same walk as a plain entry-to-return SRr spec (the node absorbed; for a path the model does not see).     *)
Definition mod_post (W : world tfibsegs) (regs : bvmap 5 word) (mem : word -> option byte) (md : Model) (sz : Z)
  : world tfibsegs -> config -> Prop :=
let H := w_H W in let sp := bv_unsigned (getr regs 2) in let nZ := page_round_up_Z sz in
fun W' c' => W' = W /\ exists (a : Z) (regs' : bvmap 5 word) (mem' : word -> option byte) (mat : list word),
  let mdN := with_vm_backing (m_vm_lazy md) mat md in
  let md1 := with_mmap_backing (w64 34) (w64 a) (w64 nZ) (mmap_model (w64 a) (w64 nZ) mdN) in
  0 <= a < 2 ^ 64 /\ grant_ok_na_pin mdN (w64 a) nZ = true /\
  c' = mkCfg (mkst regs' (getr regs 1) mem' (seg_rom tfibsegs)) md1 /\
  regs_preserved regs regs' /\ getr regs' 10 = w64 a /\
  (forall x : word, ~ (sp - MOD_STK <= bv_unsigned x < sp) -> ~ (a <= bv_unsigned x < a + nZ) -> mem' x = mem x) /\
  (forall x : word, a <= bv_unsigned x < a + nZ -> mem' x = Some (Z_to_bv 8 0)) /\
  (forall b, apresent H mem b -> apresent H mem' b) /\
  YG0d.same_io md md1.
Lemma mmapordie_granted : forall (W : world tfibsegs) (regs : bvmap 5 word) (mem : word -> option byte) (md : Model) (sz : Z),
let H := w_H W in let m := mrestrict H mem in let sp := bv_unsigned (getr regs 2) in
let nZ := page_round_up_Z sz in
getr regs 10 = w64 sz -> YK0s.ret_ok (getr regs 1) -> 0 < sz -> sz < 2 ^ 48 ->
val_mem tfibsegs m 0x9d9b0 8 0x135b60 -> val_mem tfibsegs m 0x135b60 8 4096 ->
val_mem tfibsegs m 0x9d9c0 8 0x137be8 -> val_mem tfibsegs m 0x137cec 1 0 -> val_mem tfibsegs m 0x137c78 8 0 ->
MWF md ->
(forall mat, Z.of_nat (length mat) * page_size <= A_bytes (w_A W) ->
   mmap_grant_refusable (w64 34) (with_vm_backing (m_vm_lazy md) mat md) nZ = false) ->
(forall a : word, grant_ok_na_pin md a nZ = true ->
   (bv_unsigned a + nZ <= sp - MOD_STK \/ sp <= bv_unsigned a) /\ (bv_unsigned a + nZ <= 0x9d000 \/ 0x5fb000 <= bv_unsigned a)) ->
sp mod 16 = 0 -> TFIB_IMG_END <= sp - MOD_STK -> (forall b, sp - MOD_STK <= b < sp -> apresent H mem b) ->
SRr tfibsegs W (mkCfg (mkst regs (w64 0x670d4) mem (seg_rom tfibsegs)) md)
(fun W' c' => W' = W /\ exists (a : Z) (regs' : bvmap 5 word) (mem' : word -> option byte) (mat : list word),
  let mdN := with_vm_backing (m_vm_lazy md) mat md in
  let md1 := with_mmap_backing (w64 34) (w64 a) (w64 nZ) (mmap_model (w64 a) (w64 nZ) mdN) in
  0 <= a < 2 ^ 64 /\ grant_ok_na_pin mdN (w64 a) nZ = true /\
  c' = mkCfg (mkst regs' (getr regs 1) mem' (seg_rom tfibsegs)) md1 /\
  regs_preserved regs regs' /\ getr regs' 10 = w64 a /\
  (forall x : word, ~ (sp - MOD_STK <= bv_unsigned x < sp) -> ~ (a <= bv_unsigned x < a + nZ) -> mem' x = mem x) /\
  (forall x : word, a <= bv_unsigned x < a + nZ -> mem' x = Some (Z_to_bv 8 0)) /\
  (forall b, apresent H mem b -> apresent H mem' b) /\
  YG0d.same_io md md1).
Proof.
intros W regs mem md sz. cbv zeta.
intros H10 Hra Hsz0 Hsz1 HPSP HPS HFLP HDPM HMLM HMWF HGR HAP Hal Hsp HPRES.
eapply SRr_mono.
- apply (amreal_SRr tfibsegs (IAsk (KMmapSec 0) init_state (fun _ : Z => IRet tt)) W _ (fun _ => mod_post W regs mem md sz)).
  + apply (mmapordie_node_b (fun _ : Z => IRet tt) (fun _ => mod_post W regs mem md sz) init_state 0 W regs mem md sz
      H10 Hra Hsz0 Hsz1 HPSP HPS HFLP HDPM HMLM HMWF HGR HAP Hal Hsp HPRES).
    intros a regs' mem' mat. cbv zeta. intros Ha G R1 R2 R3 R4 R5 R6. cbn [amreal].
    apply (SRr_ret tfibsegs). unfold mod_post. cbv zeta. split; [reflexivity|].
    exists a, regs', mem', mat. exact (conj Ha (conj G (conj eq_refl (conj R1 (conj R2 (conj R3 (conj R4 (conj R5 R6)))))))).
  + cbn [asafe]. intros z _. exact I.
  + cbn [agprog is_spin]. split; [reflexivity | intros z _; exact I].
  + reflexivity.
- intros W' c' _ (r & tr & _ & HP). exact HP.
Qed.

(* ---------------------------------------------------------------------------------------------------------------- *)
(* 8. The premises from the facts a caller has.                                                                      *)
(* the no-refusal premise from the room and one grantable base *)
Lemma mmap_not_refusable_of_room : forall (W : world tfibsegs) (md : Model) (nZ : Z),
eager_used md + A_bytes (w_A W) + nZ <= vm_limit (m_vmmaps md) ->
(exists a0, grant_ok_na_pin md (w64 a0) nZ = true) ->
forall mat, Z.of_nat (length mat) * page_size <= A_bytes (w_A W) ->
mmap_grant_refusable (w64 34) (with_vm_backing (m_vm_lazy md) mat md) nZ = false.
Proof.
intros W md nZ Hroom [a0 Ha0] mat Hmat.
apply (grant_na_pin_not_grant_refusable (w64 34) _ (w64 a0) nZ).
- exact Ha0.
- unfold mmap_noreserve_backed_ok. change (mmap_noreserve_b (w64 34)) with false. cbv iota. apply Z.leb_le.
  rewrite vm_backing_used_split, eager_used_wvb, m_vm_materialized_wvb, m_vmmaps_wvb. lia.
Qed.
(* the apartness premise from the reserved image segments and the mmap top below the stack window *)
Lemma mmap_apart_of_layout : forall (md : Model) (nZ sp : Z),
vm_reserved (m_vmmaps md) = segments_reserved tfibsegs ->
alloc_top (m_vmmaps md) <= sp - MOD_STK -> 0 < nZ ->
forall a : word, grant_ok_na_pin md a nZ = true ->
(bv_unsigned a + nZ <= sp - MOD_STK \/ sp <= bv_unsigned a) /\ (bv_unsigned a + nZ <= 0x9d000 \/ 0x5fb000 <= bv_unsigned a).
Proof.
intros md nZ sp Hres Htop HnZ a Hg.
destruct (grant_pin_parts _ _ _ Hg) as (G1 & G2 & G3 & G4).
pose proof (alloc_top_lt (m_vmmaps md)) as ATL.
split; [left; lia|].
rewrite Hres, region_free_app in G4. apply andb_prop in G4 as [G4 _].
assert (I1 : In (Z_to_bv 64 0x9d000, Z_to_bv 64 0x2000) (segments_reserved tfibsegs))
  by (vm_compute; repeat (first [left; reflexivity | right])).
assert (I2 : In (Z_to_bv 64 0x9f000, Z_to_bv 64 0x55c000) (segments_reserved tfibsegs))
  by (vm_compute; repeat (first [left; reflexivity | right])).
pose proof (region_free_In _ _ _ _ _ G4 I1) as D1. pose proof (region_free_In _ _ _ _ _ G4 I2) as D2.
rewrite !unsigned_lit_small in D1, D2 by lia.
lia.
Qed.
End a.
