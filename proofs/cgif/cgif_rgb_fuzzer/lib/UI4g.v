(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OssFuzzTheorems.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import
YK11 YK0i YK0j YK14 YK1b YK1a YK15 YN06 YK0s YK0p.
From OssFuzzTheorems.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import
YQ0j YQ0c YQ0b YQ03 YQ0i YQ0h YQ09 YQ04 YQ05 YQ0e YQ02 YQ00.
From OssFuzzTheorems.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YO3v YN02.
From OssFuzzTheorems.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YP0j YP0g YP0r YP0u YP0c YP0d YP0e.
From OssFuzzTheorems.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import UH04 UH07 UH06 YI00 YI02 YI01 YI03 YI05
UI1e UI1i UI57 YI07 YP14 YP15 YP13 YI08 YI0c YI0g UI3h UI3d
UI4v UI46.
From OssFuzzTheorems.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YN05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Open Scope bv_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope Z_scope.
Section c. Context {fx : YK11.FPState} {rc : YN05.RunCeil}.
Section J.
Variable B : malloc_syms.
Variable MR : MR_t.
Hypothesis LAWS : MR_laws B MR.
Hypothesis errno_low : errno_addr B + 4 <= alloc_ceiling.
Hypothesis IMG : img_laws B MR.
Local Notation segs := (ms_segs B).
Theorem cg_realloc : realloc_realizes B MR ->
forall pc STK sp0 FP L A mem md Lc Ac regs_c memc mdc pa nold n,
ms_realloc B = Some pc ->
journal B MR STK sp0 FP L A mem md Lc Ac memc mdc ->
In (pa, nold) (blocks Lc Ac) ->
getr regs_c 10 = Z_to_bv 64 pa -> getr regs_c 11 = Z_to_bv 64 n ->
MMAP_THRESHOLD <= n -> MMAP_THRESHOLD < nold -> nold + PGSZ <= n < 2 ^ 62 ->
YK0s.ret_ok (getr regs_c 1) -> spZ regs_c mod 16 = 0 ->
sp0 - STK <= spZ regs_c - REALLOC_STACK -> spZ regs_c <= sp0 ->
getr regs_c 4 = Z_to_bv 64 (ms_tp B) ->
(In (pa, nold) (blocks L A) -> forall i, 0 <= i < nold -> inFP FP (pa + i)) ->
SR segs (mkCfg (mkst regs_c (Z_to_bv 64 pc) memc (seg_rom segs)) mdc)
(fun c' => exists L2 A2 regs2 mem2 md2 (res : Z),
c' = mkCfg (mkst regs2 (getr regs_c 1) mem2 (seg_rom segs)) md2 /\
journal B MR STK sp0 FP L A mem md L2 A2 mem2 md2 /\
regs_preserved regs_c regs2 /\
getr regs2 10 = Z_to_bv 64 res /\
(exists b1 b2, blocks Lc Ac = b1 ++ (pa, nold) :: b2 /\
((res = 0 /\ blocks L2 A2 = blocks Lc Ac /\
(forall a m i, In (a, m) (blocks Lc Ac) -> 0 <= i < m -> mbyte segs mem2 (a + i) = mbyte segs memc (a + i)))
\/ (res <> 0 /\ res mod 16 = 0 /\
(exists c1 c2, c1 ++ c2 = b1 ++ b2 /\ blocks L2 A2 = c1 ++ (res, n) :: c2) /\
(forall a m i, In (a, m) (b1 ++ b2) -> 0 <= i < m -> mbyte segs mem2 (a + i) = mbyte segs memc (a + i))))) /\
(forall a, alloc_ceiling <= a < 2 ^ 64 -> ~ (spZ regs_c - REALLOC_STACK <= a < spZ regs_c) ->
mbyte segs mem2 a = mbyte segs memc a /\ (writable_at segs memc a <-> writable_at segs mem2 a))).
Proof.
intros HRE pc STK sp0 FP L A mem md Lc Ac regs_c memc mdc pa nold n Hpc HJ Hin Ha0 Ha1 Hth Hbig Hrange Hra Hal16 Hlo Hhi Htp HFP.
pose proof HJ as (HH & Hvm & Hhigh & Hblk & Hgone & Hst & Herr & Himg).
pose proof (proj1 alloc_ceiling_val) as Hac. pose proof errno_low as Hel.
assert (REALLOC_STACK = 8256) as Has by reflexivity.
destruct Hst as (Hal & Hstk0 & Hceil & H63 & Hstw).
destruct HH as (HM & HW & HB).
apply blocks_In in Hin as (p & Hp & Hpin).
assert (Hpre : call_pre_k B MR REALLOC_STACK Lc Ac regs_c memc mdc).
{ split; [exact HM|]. split; [exact HW|]. split; [exact HB|]. split; [exact Hra|].
split; [exact Hal16|]. split; [lia|]. split; [lia|]. split.
{ intros a Ha. apply Hstw. lia. }
split; [exact Htp|]. split; [exact Herr|].
intros Hf. rewrite (init_done_of_block Ac (p, nold) HW Hpin) in Hf. discriminate. }
rewrite <- Hp in Ha0.
eapply SR_mono; [eapply (realloc_SR B MR HRE); [exact Hpc | exact Hpre | exact Hpin | exact Ha0 | exact Ha1 | exact Hth | exact Hbig | exact Hrange]|].
intros c' ([q A2] & tr & Hcp & (L2 & regs2 & mem2 & md2 & -> & Hpost & Hres)). cbn [fst snd] in *.
pose proof Hpost as (HM2 & HW2 & HB2 & Hle & Hstab & Hregs & Hvm2 & Hfr & Hkeep & Hscr).
assert (HH2 : heap_ok MR L2 A2 mem2 md2) by (split; [exact HM2 | split; assumption]).
apply cpath_yields in Hcp.
pose proof (realloc_blocks Ac p nold n tr q A2 HW Hpin Hth ltac:(lia) Hcp) as Hb.
destruct (in_split _ _ Hpin) as (k1 & k2 & Ek).
assert (Hhighc : forall a, alloc_ceiling <= a < 2 ^ 64 -> ~ (spZ regs_c - REALLOC_STACK <= a < spZ regs_c) ->
mbyte segs mem2 a = mbyte segs memc a /\ (writable_at segs memc a <-> writable_at segs mem2 a)).
{ intros a Ha Hns. apply Hfr.
- left. lia.
- intros Ho. pose proof (mr_owned_low B MR LAWS _ _ _ _ a HM Ho). lia.
- intros Ho. pose proof (mr_owned_low B MR LAWS _ _ _ _ a HM2 Ho). lia.
- unfold scratch_k. intros [Hs|Hs]; [exact (Hns Hs) | lia].
- cbn beta. intros He. destruct (mr_blocks B MR LAWS Lc Ac memc mdc p nold 0 HM Hpin ltac:(lia)) as (_ & _ & Hc & _). lia. }
assert (HE1 : forall a, ptr_addr Lc p <= a < ptr_addr Lc p + nold ->
exists b m, In (b, m) (blocks Lc Ac) /\ b <= a < b + m /\ (inFP FP a \/ ~ In (b, m) (blocks L A))).
{ intros a Ha. exists (ptr_addr Lc p), nold. split; [apply blocks_In; exists p; auto|]. split; [lia|].
destruct (in_dec zz_eq_dec (ptr_addr Lc p, nold) (blocks L A)) as [H0|H0]; [|right; exact H0].
left. replace a with (ptr_addr Lc p + (a - ptr_addr Lc p)) by lia. rewrite Hp. apply HFP; [rewrite <- Hp; exact H0 | lia]. }
exists L2, A2, regs2, mem2, md2.
destruct q as [q|].
- destruct Hres as (Hr10 & Hnz & (l1 & l2 & m1 & m2 & E1 & E12 & E2) & _).
assert (I12 : incl (m1 ++ m2) (user_blocks Ac)) by (rewrite E12, E1; intros x Hx; apply in_app_iff in Hx; apply in_app_iff; destruct Hx; [left | right; right]; assumption).
assert (I12' : incl (m1 ++ m2) (user_blocks A2)) by (rewrite E2; intros x Hx; apply in_app_iff in Hx; apply in_app_iff; destruct Hx; [left | right; right]; assumption).
assert (HJ2 : journal B MR STK sp0 FP L A mem md L2 A2 mem2 md2).
{ eapply (journal_call_k B MR LAWS errno_low IMG REALLOC_STACK); [exact HJ | exact Hpost | lia | exact Hlo | exact Hhi | exact HE1 |].
intros q0 m i Hq Hnq Hi. cbn beta. rewrite E1 in Hq. apply in_app_iff in Hq as [Hq|[Hq|Hq]].
+ exfalso. apply Hnq, I12'. rewrite E12. apply in_app_iff. left. exact Hq.
+ injection Hq as -> ->. lia.
+ exfalso. apply Hnq, I12'. rewrite E12. apply in_app_iff. right. exact Hq. }
exists (ptr_addr L2 q). split; [reflexivity|]. split; [exact HJ2|]. split; [exact Hregs|]. split; [exact Hr10|]. split; [|exact Hhighc].
exists (map (fun b : sptr * Z => (ptr_addr Lc (fst b), snd b)) l1), (map (fun b : sptr * Z => (ptr_addr Lc (fst b), snd b)) l2).
split; [unfold blocks; rewrite E1, map_app; cbn [map fst snd]; rewrite Hp; reflexivity|].
right. split; [exact Hnz|]. split.
{ eapply (mr_blocks_aligned B MR LAWS); [exact HM2 |]. rewrite E2. apply in_app_iff. right. left. reflexivity. }
assert (Hmap : forall l, incl l (m1 ++ m2) -> map (fun b : sptr * Z => (ptr_addr L2 (fst b), snd b)) l = map (fun b : sptr * Z => (ptr_addr Lc (fst b), snd b)) l).
{ intros l Hl. apply (map_addr_stable Lc L2 l (m1 ++ m2) Hl). intros q0 m Hq. apply (Hstab q0 m); [apply I12; exact Hq | apply I12'; exact Hq]. }
split.
+ exists (map (fun b : sptr * Z => (ptr_addr Lc (fst b), snd b)) m1), (map (fun b : sptr * Z => (ptr_addr Lc (fst b), snd b)) m2).
split; [rewrite <- !map_app, E12; reflexivity|].
unfold blocks. rewrite E2, map_app. cbn [map fst snd].
rewrite <- (Hmap m1), <- (Hmap m2); [reflexivity | intros x Hx; apply in_app_iff; right; exact Hx | intros x Hx; apply in_app_iff; left; exact Hx].
+ intros a m i Ham Hi. rewrite <- map_app, <- E12, in_map_iff in Ham. destruct Ham as ([q0 m0] & Eq & Hq0). cbn [fst snd] in Eq. injection Eq as <- <-.
apply (Hkeep q0 m0 i); [apply I12; exact Hq0 | apply I12'; exact Hq0 | exact Hi].
- destruct Hres as [Hr10 Eub].
assert (HJ2 : journal B MR STK sp0 FP L A mem md L2 A2 mem2 md2).
{ eapply (journal_call_k B MR LAWS errno_low IMG REALLOC_STACK); [exact HJ | exact Hpost | lia | exact Hlo | exact Hhi | exact HE1 |].
intros q0 m i Hq Hnq Hi. exfalso. apply Hnq. rewrite Eub. exact Hq. }
exists 0. split; [reflexivity|]. split; [exact HJ2|]. split; [exact Hregs|]. split; [exact Hr10|]. split; [|exact Hhighc].
exists (map (fun b : sptr * Z => (ptr_addr Lc (fst b), snd b)) k1), (map (fun b : sptr * Z => (ptr_addr Lc (fst b), snd b)) k2).
split; [unfold blocks; rewrite Ek, map_app; cbn [map fst snd]; rewrite Hp; reflexivity|].
left. split; [reflexivity|]. split.
+ unfold blocks. rewrite Eub. apply (map_addr_stable Lc L2 (user_blocks Ac) (user_blocks Ac)); [intros x Hx; exact Hx|].
intros q0 m Hq. apply (Hstab q0 m Hq). rewrite Eub. exact Hq.
+ intros a m i Ham Hi. apply blocks_In in Ham as (q0 & Hq & Hq0). rewrite <- Hq.
apply (Hkeep q0 m i Hq0); [rewrite Eub; exact Hq0 | exact Hi].
Qed.
Lemma jrealloc_at : realloc_realizes B MR ->
forall pc E ss ms STK sp0 FP L A mem md Lc Ac mdc pa nold n spc raw,
ms_realloc B = Some pc ->
st_ok segs E ss ms -> ss_pc ss = pc -> ss_resv ss = None ->
journal B MR STK sp0 FP L A mem md Lc Ac (ms_mem ms) mdc ->
In (pa, nold) (blocks Lc Ac) -> ~ In (pa, nold) (blocks L A) ->
getr (ms_regs ms) 10 = Z_to_bv 64 pa -> getr (ms_regs ms) 11 = Z_to_bv 64 n ->
MMAP_THRESHOLD <= n -> MMAP_THRESHOLD < nold -> nold + PGSZ <= n < 2 ^ 62 ->
getr (ms_regs ms) 2 = Z_to_bv 64 spc -> 0 <= spc < 2 ^ 64 -> spc mod 16 = 0 ->
sp0 - STK <= spc - REALLOC_STACK -> spc <= sp0 ->
getr (ms_regs ms) 4 = Z_to_bv 64 (ms_tp B) ->
getr (ms_regs ms) 1 = raw -> YK0s.ret_ok raw ->
SR segs (mkCfg ms mdc)
(fun c' => exists L2 A2 regs2 mem2 md2 (res : Z),
c' = mkCfg (mkst regs2 raw mem2 (seg_rom segs)) md2 /\
journal B MR STK sp0 FP L A mem md L2 A2 mem2 md2 /\
regs_preserved (ms_regs ms) regs2 /\
getr regs2 10 = Z_to_bv 64 res /\
(exists b1 b2, blocks Lc Ac = b1 ++ (pa, nold) :: b2 /\
((res = 0 /\ blocks L2 A2 = blocks Lc Ac /\
(forall a m i, In (a, m) (blocks Lc Ac) -> 0 <= i < m -> mbyte segs mem2 (a + i) = mbyte segs (ms_mem ms) (a + i)))
\/ (res <> 0 /\ res mod 16 = 0 /\
(exists c1 c2, c1 ++ c2 = b1 ++ b2 /\ blocks L2 A2 = c1 ++ (res, n) :: c2) /\
(forall a m i, In (a, m) (b1 ++ b2) -> 0 <= i < m -> mbyte segs mem2 (a + i) = mbyte segs (ms_mem ms) (a + i))))) /\
(forall x, alloc_ceiling <= x < 2 ^ 64 -> ~ (spc - REALLOC_STACK <= x < spc) ->
mbyte segs mem2 x = mbyte segs (ms_mem ms) x /\
(writable_at segs (ms_mem ms) x <-> writable_at segs mem2 x))).
Proof.
intros HRE pc E ss ms STK sp0 FP L A mem md Lc Ac mdc pa nold n spc raw
Hpc HS Hsspc Hrv HJ Hin Hnot Ha0 Ha1 Hth Hbig Hrange Hsp Hspc Hal Hlo Hhi Htp Hra Hraw.
assert (Hsp' : spZ (ms_regs ms) = spc).
{ unfold spZ. rewrite Hsp. apply unsigned_lit_small. exact Hspc. }
rewrite (st_ok_mkst segs E ss ms HS Hrv), Hsspc.
eapply SR_mono.
{ eapply (cg_realloc HRE pc STK sp0 FP L A mem md Lc Ac (ms_regs ms) (ms_mem ms) mdc pa nold n Hpc HJ Hin Ha0 Ha1 Hth Hbig Hrange).
- rewrite Hra. exact Hraw.
- rewrite Hsp'. exact Hal.
- rewrite Hsp'. exact Hlo.
- rewrite Hsp'. exact Hhi.
- exact Htp.
- intros H0. exfalso. exact (Hnot H0). }
intros c' (L2 & A2 & regs2 & mem2 & md2 & res & -> & HJ2 & HP2 & Hr10 & Hres & Hhi2).
exists L2, A2, regs2, mem2, md2, res. rewrite Hra. split; [reflexivity|]. split; [exact HJ2|]. split; [exact HP2|].
split; [exact Hr10|]. split; [exact Hres|].
intros x Hx Hnx. apply Hhi2; [exact Hx|]. rewrite Hsp'. exact Hnx.
Qed.
End J.
Definition rbk (old : Z * Z) (res n : Z) : Z * Z := if res =? 0 then old else (res, n).

Lemma malloc_post_perm : forall (old blk2 blkc : list (Z * Z)) res n (Wt : Prop),
Permutation blkc old ->
(res = 0 /\ blk2 = blkc) \/ (res <> 0 /\ res mod 16 = 0 /\ (exists b1 b2, blk2 = b1 ++ (res, n) :: b2 /\ blkc = b1 ++ b2) /\ Wt) ->
Permutation blk2 (old ++ optb res n) /\ (forall x, In x blkc -> In x blk2).
Proof.
intros old blk2 blkc res n Wt HP [[-> ->] | (Hnz & _ & (b1 & b2 & -> & ->) & _)].
- unfold optb. rewrite Z.eqb_refl, app_nil_r. split; [exact HP | intros x Hx; exact Hx].
- unfold optb. destruct (Z.eqb_spec res 0) as [Hc|Hc]; [lia|]. split.
+ eapply Permutation_trans; [apply Permutation_sym, Permutation_middle|].
eapply Permutation_trans; [| apply Permutation_cons_append]. apply perm_skip. exact HP.
+ intros x Hx. apply in_app_iff in Hx. apply in_app_iff. destruct Hx as [Hx|Hx]; [left; exact Hx | right; right; exact Hx].
Qed.
Lemma realloc_post_perm : forall (old : list (Z * Z)) (ob : Z * Z) (blk2 blkc : list (Z * Z)) (m m' : word -> option byte) res n,
Permutation blkc (old ++ [ob]) ->
(exists b1 b2, blkc = b1 ++ ob :: b2 /\
((res = 0 /\ blk2 = blkc /\ (forall a k i, In (a, k) blkc -> 0 <= i < k -> mbyte ubs2segs m' (a + i) = mbyte ubs2segs m (a + i)))
\/ (res <> 0 /\ res mod 16 = 0 /\ (exists c1 c2, c1 ++ c2 = b1 ++ b2 /\ blk2 = c1 ++ (res, n) :: c2) /\
(forall a k i, In (a, k) (b1 ++ b2) -> 0 <= i < k -> mbyte ubs2segs m' (a + i) = mbyte ubs2segs m (a + i))))) ->
Permutation blk2 (old ++ [rbk ob res n]) /\ (forall a k i, In (a, k) old -> 0 <= i < k -> mbyte ubs2segs m' (a + i) = mbyte ubs2segs m (a + i)).
Proof.
intros old ob blk2 blkc m m' res n HP (b1 & b2 & Eb & Hc).
assert (Hold : Permutation (b1 ++ b2) old).
{ rewrite <- (app_nil_r old). apply (Permutation_app_inv b1 b2 old [] ob). rewrite <- Eb. exact HP. }
unfold rbk. destruct Hc as [(-> & -> & Hk) | (Hnz & _ & (c1 & c2 & E12 & ->) & Hk)].
- rewrite Z.eqb_refl. split; [exact HP|]. intros a k i Ha Hi. apply (Hk a k i); [|exact Hi]. eapply Permutation_in; [apply Permutation_sym; exact HP|]. apply in_app_iff. left. exact Ha.
- destruct (Z.eqb_spec res 0) as [|_]; [lia|]. split.
+ eapply Permutation_trans; [apply Permutation_sym, Permutation_middle|]. eapply Permutation_trans; [|apply Permutation_cons_append]. apply perm_skip. rewrite E12. exact Hold.
+ intros a k i Ha Hi. apply (Hk a k i); [|exact Hi]. eapply Permutation_in; [apply Permutation_sym; exact Hold|]. exact Ha.
Qed.
Definition PC_LD : Z := Eval vm_compute in (ubs2_A_cgif_rgb_addframe + 0x684).
Definition PC_R1 : Z := Eval vm_compute in (ubs2_A_cgif_rgb_addframe + 0x698).
Definition PC_R2 : Z := Eval vm_compute in (ubs2_A_cgif_rgb_addframe + 0x6ac).
Definition PC_M3 : Z := Eval vm_compute in (ubs2_A_cgif_rgb_addframe + 0x6b8).
Definition PC_M4 : Z := Eval vm_compute in (ubs2_A_cgif_rgb_addframe + 0x6c4).
Definition PC_M5 : Z := Eval vm_compute in (ubs2_A_cgif_rgb_addframe + 0x6d0).
Definition PC_C0 : Z := Eval vm_compute in (ubs2_A_cgif_rgb_addframe + 0x6e8).
Definition PC_FAIL : Z := Eval vm_compute in (ubs2_A_cgif_rgb_addframe + 0x1364).
Definition PC_MS : Z := Eval vm_compute in (ubs2_A_cgif_rgb_addframe + 0x704).
Definition PC_REH : Z := Eval vm_compute in (ubs2_A_cgif_rgb_addframe + 0x734).
Definition PC_POST : Z := Eval vm_compute in (ubs2_A_cgif_rgb_addframe + 0x904).
Section d.
Variable API : AllocAPI ubs2_msyms.
Variables (L : layout) (A : astate) (regs0 : bvmap 5 word) (mem0 : word -> option byte) (md0 : Model).
Variables (r cfp g wfn ctx path attr gen loops W H bef beffmt cur : Z) (s : cgif_st) (N : Z).
Variables (img fmt fattr fgen delay : Z) (rest : list (Z * Z)).
Local Notation RINV := (rgba_inv API L A regs0 mem0 md0 r cfp g W H bef beffmt s N img fmt fattr fgen delay rest).
Local Notation SP := (sp regs0).
Local Notation BASE0 := (BASE r g N img fmt rest s bef beffmt).
Definition keepb (pnew fimg : Z) (C : cht) : list (Z * Z) :=
BASE0 ++ [(pnew, fmt * N); (fimg, N)] ++ [(ch_c C, CHT_SIZE); (ch_f C, 4 * ch_T C); (ch_h C, 3 * ch_T C); (ch_u C, ch_T C)].
Definition rz_blocks (Lc : layout) (Ac : astate) (pnew fimg : Z) (C : cht) (extra : list (Z * Z)) : Prop :=
Permutation (blocks Lc Ac) (keepb pnew fimg C ++ extra).
Definition rz_mem (memc : word -> option byte) (i ha pnew fimg : Z) (imgl : list Z) (C : cht) : Prop :=
slots_mid regs0 cfp N memc pnew fimg /\ slot regs0 memc SL_32 65280 /\ slot regs0 memc SL_40 fmt /\ slot regs0 memc SL_56 N /\
slot regs0 memc SL_64 1 /\ slot regs0 memc SL_80 (2 ^ 32 - 1) /\ slot regs0 memc SL_112 fmt /\ slot regs0 memc SL_120 img /\
fcfg_at regs0 fattr delay memc fimg 0 0 /\ rgb_obj r g wfn ctx path attr gen loops W H bef beffmt cur memc /\ cgif_at memc g s /\
img_at N img fmt memc imgl /\ pnew <> 0 /\ fimg <> 0 /\
arr32 ubs2segs memc (ch_f C) (ht_frequ (ch_H C)) /\ arr8 ubs2segs memc (ch_h C) (ht_keys (ch_H C)) /\ arr8 ubs2segs memc (ch_u C) (ht_used (ch_H C)) /\
ht_inv (ch_H C) (ch_ent C) /\ ht_T (ch_H C) = ch_T C /\ In (ch_T C) ts_chain /\ ch_T C < MAX_TABLE_SIZE /\
0 <= ch_hS C < 2 ^ 64 /\ 0 <= ch_uS C < 2 ^ 64 /\ 0 <= ch_TS C < 2 ^ 32 /\
ch_hS C = ch_h C /\ ch_uS C = ch_u C /\ ch_TS C = ch_T C   /\ zsum (map snd (ch_ent C)) <= i + 1.
Definition rz_struct (memc : word -> option byte) (C : cht) (pf xf cnt : Z) : Prop :=
obj_at ubs2segs memc (ch_c C) LAY_Cht [ch_f C; ch_hS C; ch_uS C; pf; xf; cnt; ch_TS C].
Definition rz_facts (i ha T' : Z) (C : cht) : Prop :=
(fmt = 3 \/ fmt = 4) /\ 0 <= i < N /\ (ha = 0 \/ (ha = 1 /\ fmt = 4)) /\ T' = getNextPrimePower2 (ch_T C).
Definition rz_regs (regs1 : bvmap 5 word) (i ha : Z) (C : cht) : Prop :=
rgba_regs regs0 regs1 /\ getr regs1 9 = Z_to_bv 64 i /\ getr regs1 20 = Z_to_bv 64 (ch_c C) /\ getr regs1 8 = Z_to_bv 64 r /\
getr regs1 21 = Z_to_bv 64 2.
Definition at_LD (regs1 : bvmap 5 word) (Lc : layout) (Ac : astate) (memc : word -> option byte) (mdc : Model)
(i ha pnew fimg : Z) (imgl : list Z) (C : cht) : Prop :=
RINV Lc Ac memc mdc /\ rgba_regs regs0 regs1 /\ (fmt = 3 \/ fmt = 4) /\ 0 <= i < N /\ (ha = 0 \/ (ha = 1 /\ fmt = 4)) /\
getr regs1 9 = Z_to_bv 64 i /\ getr regs1 20 = Z_to_bv 64 (ch_c C) /\ getr regs1 8 = Z_to_bv 64 r /\ getr regs1 21 = Z_to_bv 64 2 /\
ch_T C < MAX_TABLE_SIZE /\ slot regs0 memc SL_72 ha /\
hist_mem regs0 r cfp g wfn ctx path attr gen loops W H bef beffmt cur s N img fmt fattr delay rest Lc Ac memc pnew fimg imgl C (i + 1) /\
getr regs1 19 = Z_to_bv 64 (getNextPrimePower2 (ch_T C)).
Definition at_R1 (regs1 : bvmap 5 word) (Lc : layout) (Ac : astate) (memc : word -> option byte) (mdc : Model)
(i ha pnew fimg : Z) (imgl : list Z) (C : cht) (T' p1 : Z) : Prop :=
RINV Lc Ac memc mdc /\ rz_facts i ha T' C /\ rz_regs regs1 i ha C /\
getr regs1 10 = Z_to_bv 64 p1 /\ getr regs1 24 = Z_to_bv 64 (3 * T') /\ getr regs1 19 = Z_to_bv 64 T' /\
rz_mem memc i ha pnew fimg imgl C /\ slot regs0 memc SL_72 ha /\ rz_struct memc C (ch_p C) (ch_x C) (ht_cnt (ch_H C)) /\
rz_blocks Lc Ac pnew fimg C [rbk (ch_p C, 3 * ch_T C) p1 (3 * T'); (ch_x C, 4 * ch_T C)].
Definition at_R2 (regs1 : bvmap 5 word) (Lc : layout) (Ac : astate) (memc : word -> option byte) (mdc : Model)
(i ha pnew fimg : Z) (imgl : list Z) (C : cht) (T' p1 x1 : Z) : Prop :=
RINV Lc Ac memc mdc /\ rz_facts i ha T' C /\ rz_regs regs1 i ha C /\
getr regs1 10 = Z_to_bv 64 x1 /\ getr regs1 27 = Z_to_bv 64 p1 /\ getr regs1 26 = Z_to_bv 64 (4 * T') /\ getr regs1 24 = Z_to_bv 64 (3 * T') /\
getr regs1 19 = Z_to_bv 64 T' /\
rz_mem memc i ha pnew fimg imgl C /\ slot regs0 memc SL_72 ha /\ rz_struct memc C (ch_p C) (ch_x C) (ht_cnt (ch_H C)) /\
rz_blocks Lc Ac pnew fimg C [rbk (ch_p C, 3 * ch_T C) p1 (3 * T'); rbk (ch_x C, 4 * ch_T C) x1 (4 * T')].
Definition at_M3 (regs1 : bvmap 5 word) (Lc : layout) (Ac : astate) (memc : word -> option byte) (mdc : Model)
(i ha pnew fimg : Z) (imgl : list Z) (C : cht) (T' p1 x1 h1 : Z) : Prop :=
RINV Lc Ac memc mdc /\ rz_facts i ha T' C /\ rz_regs regs1 i ha C /\
getr regs1 10 = Z_to_bv 64 h1 /\ getr regs1 22 = Z_to_bv 64 x1 /\ getr regs1 27 = Z_to_bv 64 p1 /\ getr regs1 26 = Z_to_bv 64 (4 * T') /\
getr regs1 19 = Z_to_bv 64 T' /\
rz_mem memc i ha pnew fimg imgl C /\ slot regs0 memc SL_72 ha /\ rz_struct memc C (ch_p C) (ch_x C) (ht_cnt (ch_H C)) /\
rz_blocks Lc Ac pnew fimg C ([rbk (ch_p C, 3 * ch_T C) p1 (3 * T'); rbk (ch_x C, 4 * ch_T C) x1 (4 * T')] ++ optb h1 (3 * T')).
Definition at_M4 (regs1 : bvmap 5 word) (Lc : layout) (Ac : astate) (memc : word -> option byte) (mdc : Model)
(i ha pnew fimg : Z) (imgl : list Z) (C : cht) (T' p1 x1 h1 u1 : Z) : Prop :=
RINV Lc Ac memc mdc /\ rz_facts i ha T' C /\ rz_regs regs1 i ha C /\
getr regs1 10 = Z_to_bv 64 u1 /\ getr regs1 24 = Z_to_bv 64 h1 /\ getr regs1 22 = Z_to_bv 64 x1 /\ getr regs1 27 = Z_to_bv 64 p1 /\
getr regs1 26 = Z_to_bv 64 (4 * T') /\ getr regs1 19 = Z_to_bv 64 T' /\
rz_mem memc i ha pnew fimg imgl C /\ slot regs0 memc SL_72 ha /\ rz_struct memc C (ch_p C) (ch_x C) (ht_cnt (ch_H C)) /\
rz_blocks Lc Ac pnew fimg C ([rbk (ch_p C, 3 * ch_T C) p1 (3 * T'); rbk (ch_x C, 4 * ch_T C) x1 (4 * T')] ++ optb h1 (3 * T') ++ optb u1 T').
Definition at_M5 (regs1 : bvmap 5 word) (Lc : layout) (Ac : astate) (memc : word -> option byte) (mdc : Model)
(i ha pnew fimg : Z) (imgl : list Z) (C : cht) (T' p1 x1 h1 u1 f1 : Z) : Prop :=
RINV Lc Ac memc mdc /\ rz_facts i ha T' C /\ rz_regs regs1 i ha C /\
getr regs1 10 = Z_to_bv 64 f1 /\ getr regs1 25 = Z_to_bv 64 u1 /\ getr regs1 24 = Z_to_bv 64 h1 /\ getr regs1 22 = Z_to_bv 64 x1 /\
getr regs1 27 = Z_to_bv 64 p1 /\ getr regs1 19 = Z_to_bv 64 T' /\
rz_mem memc i ha pnew fimg imgl C /\ slot regs0 memc SL_72 ha /\ rz_struct memc C (ch_p C) (ch_x C) (ht_cnt (ch_H C)) /\
rz_blocks Lc Ac pnew fimg C ([rbk (ch_p C, 3 * ch_T C) p1 (3 * T'); rbk (ch_x C, 4 * ch_T C) x1 (4 * T')] ++ optb h1 (3 * T') ++ optb u1 T' ++ optb f1 (4 * T')).
Definition chk_regs (regs1 : bvmap 5 word) (T' p1 x1 h1 u1 f1 : Z) : Prop :=
getr regs1 27 = Z_to_bv 64 p1 /\ getr regs1 22 = Z_to_bv 64 x1 /\ getr regs1 24 = Z_to_bv 64 h1 /\
getr regs1 25 = Z_to_bv 64 u1 /\ getr regs1 26 = Z_to_bv 64 f1 /\ getr regs1 19 = Z_to_bv 64 T'.
Definition at_FAIL (regs1 : bvmap 5 word) (Lc : layout) (Ac : astate) (memc : word -> option byte) (mdc : Model)
(i ha pnew fimg : Z) (imgl : list Z) (C : cht) (T' p1 x1 h1 u1 f1 : Z) : Prop :=
RINV Lc Ac memc mdc /\ rz_facts i ha T' C /\ rz_regs regs1 i ha C /\ chk_regs regs1 T' p1 x1 h1 u1 f1 /\
(p1 = 0 \/ x1 = 0 \/ h1 = 0 \/ u1 = 0 \/ f1 = 0) /\
rz_mem memc i ha pnew fimg imgl C /\ slot regs0 memc SL_72 ha /\ rz_struct memc C (ch_p C) (ch_x C) (ht_cnt (ch_H C)) /\
rz_blocks Lc Ac pnew fimg C ([rbk (ch_p C, 3 * ch_T C) p1 (3 * T'); rbk (ch_x C, 4 * ch_T C) x1 (4 * T')] ++ optb h1 (3 * T') ++ optb u1 T' ++ optb f1 (4 * T')).
Definition at_C0 (regs1 : bvmap 5 word) (Lc : layout) (Ac : astate) (memc : word -> option byte) (mdc : Model)
(i ha pnew fimg : Z) (imgl : list Z) (C : cht) (T' p1 x1 h1 u1 f1 : Z) : Prop :=
RINV Lc Ac memc mdc /\ rz_facts i ha T' C /\ rz_regs regs1 i ha C /\ chk_regs regs1 T' p1 x1 h1 u1 f1 /\
p1 <> 0 /\ x1 <> 0 /\ h1 <> 0 /\ u1 <> 0 /\ f1 <> 0 /\
rz_mem memc i ha pnew fimg imgl C /\ slot regs0 memc SL_72 ha /\ rz_struct memc C (ch_p C) (ch_x C) (ht_cnt (ch_H C)) /\
rz_blocks Lc Ac pnew fimg C [(p1, 3 * T'); (x1, 4 * T'); (h1, 3 * T'); (u1, T'); (f1, 4 * T')].
Section e.
Let MR : MR_t := aa_MR API.
Let LAWS : MR_laws ubs2_msyms MR := aa_laws API.
Lemma wr_byte_tmp : forall Lc Ac memc mdc (l : list (Z * Z)) b n a,
heap_ok MR Lc Ac memc mdc -> Permutation (blocks Lc Ac) (BASE0 ++ l) -> Permutation (blocks L A) BASE0 ->
In (b, n) l -> 0 < n -> b <= a < b + n ->
wr_byte RGBA_STK (sp0 regs0) (FPfoot r g bef beffmt s N) (blocks L A) (blocks Lc Ac) a.
Proof.
intros Lc Ac memc mdc l b n a HH HP HP0 Hb Hn Ha. right. right. exists b, n.
split; [eapply Permutation_in; [apply Permutation_sym; exact HP|]; apply in_app_iff; right; exact Hb|].
split; [exact (tmp_not_entry API L A Lc Ac memc mdc (b, n) BASE0 l HH HP HP0 Hb Hn) | exact Ha].
Qed.
Lemma keepb_sub : forall pnew fimg C b, In b (BASE0 ++ [(ch_f C, 4 * ch_T C); (ch_h C, 3 * ch_T C); (ch_u C, ch_T C)]) -> In b (keepb pnew fimg C).
Proof.
intros pnew fimg C b Hb. unfold keepb. apply in_app_iff in Hb. apply in_app_iff. destruct Hb as [Hb|Hb]; [left; exact Hb|].
right. apply in_app_iff. right. right. exact Hb.
Qed.
Lemma rz_mem_of_RS : forall Lc Ac memc i ha pnew fimg imgl C, ch_T C < MAX_TABLE_SIZE ->
hist_mem regs0 r cfp g wfn ctx path attr gen loops W H bef beffmt cur s N img fmt fattr delay rest Lc Ac memc pnew fimg imgl C (i + 1) ->
rz_mem memc i ha pnew fimg imgl C /\ rz_struct memc C (ch_p C) (ch_x C) (ht_cnt (ch_H C)) /\ rz_blocks Lc Ac pnew fimg C [(ch_p C, 3 * ch_T C); (ch_x C, 4 * ch_T C)].
Proof.
intros Lc Ac memc i ha pnew fimg imgl C HTlt (Hslots & S32 & S40 & S56 & S64 & S80 & S112 & S120 & Hfc & Hobj & Hcg & Himg & Hcht & EhS & EuS & ETS & Hz & Hpn & Hfi & HB).
destruct Hcht as (Hobjc & (Af & Ah & Au & Ap & Ax) & Hinv & HT & Hch & R1 & R2 & R3).
split; [| split; [exact Hobjc|]].
- unfold rz_mem. repeat (split; [assumption|]). exact Hz.
- unfold rz_blocks, keepb. eapply Permutation_trans; [exact HB|]. rewrite <- !app_assoc. apply Permutation_app_head. apply Permutation_app_head.
unfold cht_blks, cht_blocks. cbn [app]. apply Permutation_refl.
Qed.
Lemma rz_mem_ht : forall memc i ha pnew fimg imgl C, rz_mem memc i ha pnew fimg imgl C ->
ht_inv (ch_H C) (ch_ent C) /\ ht_T (ch_H C) = ch_T C /\ In (ch_T C) ts_chain /\ ch_T C < MAX_TABLE_SIZE.
Proof. intros memc i ha pnew fimg imgl C (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hinv & HT & Hch & HTlt & _). auto. Qed.
Lemma rz_mem_live : forall memc i ha pnew fimg imgl C, rz_mem memc i ha pnew fimg imgl C ->
ch_hS C = ch_h C /\ ch_uS C = ch_u C /\ ch_TS C = ch_T C.
Proof. intros memc i ha pnew fimg imgl C (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & EhS & EuS & ETS & _). auto. Qed.
Lemma rz_mem_zsum : forall memc i ha pnew fimg imgl C, rz_mem memc i ha pnew fimg imgl C -> zsum (map snd (ch_ent C)) <= i + 1.
Proof. intros memc i ha pnew fimg imgl C (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hz). exact Hz. Qed.
Lemma rz_mem_arrs : forall memc i ha pnew fimg imgl C, rz_mem memc i ha pnew fimg imgl C ->
arr32 ubs2segs memc (ch_f C) (ht_frequ (ch_H C)) /\ arr8 ubs2segs memc (ch_h C) (ht_keys (ch_H C)) /\ arr8 ubs2segs memc (ch_u C) (ht_used (ch_H C)).
Proof. intros memc i ha pnew fimg imgl C (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Af & Ah & Au & _). auto. Qed.
Lemma rz_mem_kept : forall Lc Ac (memc memX : word -> option byte) mdc i ha pnew fimg imgl C extra i',
heap_ok MR Lc Ac memc mdc -> alloc_ceiling <= SP -> SP + RGBA_FRAME <= 2 ^ 63 -> (fmt = 3 \/ fmt = 4) ->
rz_blocks Lc Ac pnew fimg C extra -> rz_mem memc i ha pnew fimg imgl C ->
(forall a, alloc_ceiling <= a < 2 ^ 64 -> SP <= a -> ~ (SP + 72 <= a < SP + 80) -> ~ (SP + 88 <= a < SP + 112) -> mbyte ubs2segs memX a = mbyte ubs2segs memc a) ->
(forall b n k, In (b, n) (BASE0 ++ [(ch_f C, 4 * ch_T C); (ch_h C, 3 * ch_T C); (ch_u C, ch_T C)]) -> 0 <= k < n -> mbyte ubs2segs memX (b + k) = mbyte ubs2segs memc (b + k)) ->
zsum (map snd (ch_ent C)) <= i' + 1 ->
rz_mem memX i' ha pnew fimg imgl C.
Proof.
intros Lc Ac memc memX mdc i ha pnew fimg imgl C extra i' HH Hsp Hsp2 Hfmt HB
(Hslots & S32 & S40 & S56 & S64 & S80 & S112 & S120 & Hfc & Hobj & Hcg & [Himg Hlen] & Hpn & Hfi & Af & Ah & Au & Hinv & HT & Hch & HTlt & R1 & R2 & R3 & EhS & EuS & ETS & Hz) KH KB Hz'.
pose proof (proj1 alloc_ceiling_val) as Hac. assert (HFv : RGBA_FRAME = 5168) by reflexivity.
pose proof (ts_chain_ok _ Hch) as (T1 & T2 & T3).
assert (KS : forall off v, 0 <= off -> off + 8 <= RGBA_FRAME -> (off + 8 <= 72 \/ 80 <= off) -> (off + 8 <= 88 \/ 112 <= off) -> slot regs0 memc off v -> slot regs0 memX off v).
{ intros off v H0 H1 H2 H3 Hs. unfold slot in *. apply (val_mem_kept8 memc); [exact Hs|]. intros k Hk. apply KH; lia. }
assert (KBk : forall (j : nat) b n k, nth_error [(ch_f C, 4 * ch_T C); (ch_h C, 3 * ch_T C); (ch_u C, ch_T C)] j = Some (b, n) -> 0 <= k < n -> mbyte ubs2segs memX (b + k) = mbyte ubs2segs memc (b + k)).
{ intros j b n k Hj Hk. apply (KB b n k); [apply in_app_iff; right; eapply nth_error_In; exact Hj | exact Hk]. }
assert (KB0 : forall y k, In y BASE0 -> 0 <= k < snd y -> mbyte ubs2segs memX (fst y + k) = mbyte ubs2segs memc (fst y + k)).
{ intros [b n] k Hy Hk. apply (KB b n k); [apply in_app_iff; left; exact Hy | exact Hk]. }
unfold rz_mem. destruct Hslots as (M8 & M16 & M24 & M48).
split. { unfold slots_mid, SL_N, SL_cfp, SL_new, SL_fimg in *. repeat split; (apply KS; [lia | lia | lia | lia | assumption]). }
split; [apply KS; unfold SL_32 in *; [lia | lia | lia | lia | exact S32]|].
split; [apply KS; unfold SL_40 in *; [lia | lia | lia | lia | exact S40]|].
split; [apply KS; unfold SL_56 in *; [lia | lia | lia | lia | exact S56]|].
split; [apply KS; unfold SL_64 in *; [lia | lia | lia | lia | exact S64]|].
split; [apply KS; unfold SL_80 in *; [lia | lia | lia | lia | exact S80]|].
split; [apply KS; unfold SL_112 in *; [lia | lia | lia | lia | exact S112]|].
split; [apply KS; unfold SL_120 in *; [lia | lia | lia | lia | exact S120]|].
split. { unfold fcfg_at in *. eapply (obj_at_transport_range ubs2segs _ _ _ _ _ 29); [exact Hfc | reflexivity |]. intros k Hk. unfold OFF_fcfg. apply KH; lia. }
split. { unfold rgb_obj in *. eapply (obj_at_transport_range ubs2segs _ _ _ _ _ RGB_SIZE); [exact Hobj | reflexivity |]. intros k Hk. apply (KB0 (r, RGB_SIZE) k); [left; reflexivity | cbn; exact Hk]. }
split. { eapply (cgif_at_kept _ _ g s N (cgif_blocks g s N) []); [rewrite app_nil_r; apply Permutation_refl | exact Hcg |].
intros b n k Hbn Hk. apply (KB0 (b, n) k); [| cbn; exact Hk]. right. apply in_app_iff. left. exact Hbn. }
split. { split; [|exact Hlen]. eapply arr8_frame; [exact Himg|]. intros a Ha. replace a with (img + (a - img)) by lia. apply (KB0 (img, fmt * N) (a - img)); [| cbn [snd]; clear - Ha Hlen; lia].
right. apply in_app_iff. right. apply in_app_iff. right. apply in_app_iff. left. unfold img_block, fmt_okb. destruct Hfmt as [-> | ->]; left; reflexivity. }
split; [exact Hpn|]. split; [exact Hfi|].
pose proof Hinv as ((L1 & L2 & L3 & L4 & L5) & _). rewrite HT in L1, L2, L3.
split. { eapply arr32_frame; [exact Af|]. intros a Ha. replace a with (ch_f C + (a - ch_f C)) by lia. apply (KBk 0%nat (ch_f C) (4 * ch_T C)); [reflexivity | lia]. }
split. { eapply arr8_frame; [exact Ah|]. intros a Ha. replace a with (ch_h C + (a - ch_h C)) by lia. apply (KBk 1%nat (ch_h C) (3 * ch_T C)); [reflexivity | lia]. }
split. { eapply arr8_frame; [exact Au|]. intros a Ha. replace a with (ch_u C + (a - ch_u C)) by lia. apply (KBk 2%nat (ch_u C) (ch_T C)); [reflexivity | lia]. }
split; [exact Hinv|]. split; [exact HT|]. split; [exact Hch|]. split; [exact HTlt|]. split; [exact R1|]. split; [exact R2|]. split; [exact R3|]. split; [exact EhS|]. split; [exact EuS|]. split; [exact ETS | exact Hz'].
Qed.
Lemma rz_struct_kept : forall (memc memX : word -> option byte) pnew fimg C pf xf cnt,
rz_struct memc C pf xf cnt ->
(forall b n k, In (b, n) (keepb pnew fimg C) -> 0 <= k < n -> mbyte ubs2segs memX (b + k) = mbyte ubs2segs memc (b + k)) ->
rz_struct memX C pf xf cnt.
Proof.
intros memc memX pnew fimg C pf xf cnt Hs KB. unfold rz_struct in *.
eapply (obj_at_transport_range ubs2segs _ _ _ _ _ CHT_SIZE); [exact Hs | reflexivity |]. intros k Hk.
apply (KB (ch_c C) CHT_SIZE k); [| exact Hk]. unfold keepb. apply in_app_iff. right. apply in_app_iff. right. left. reflexivity.
Qed.
Lemma rgba_inv_call : forall Lc Ac (memc memX : word -> option byte) mdc L2 A2 md2 l,
RINV Lc Ac memc mdc ->
journal ubs2_msyms MR RGBA_STK (sp0 regs0) (FPfoot r g bef beffmt s N) L A mem0 md0 L2 A2 memX md2 ->
Permutation (blocks L2 A2) (BASE0 ++ l) ->
(forall a, alloc_ceiling <= a < 2 ^ 64 -> SP + 5064 <= a -> mbyte ubs2segs memX a = mbyte ubs2segs memc a) ->
RINV L2 A2 memX md2.
Proof.
intros Lc Ac memc memX mdc L2 A2 md2 l (HJ & Hinit & Hfrm & Hra & Hal & Htp & HRA & Hc8 & Hclo & Hchi & Hcfp & Hro & HINV') HJ' HB2 KH.
pose proof HJ as (_ & _ & _ & _ & _ & Hstk & _). destruct Hstk as (_ & HSTK0 & Hceil & H63 & _). pose proof (proj1 alloc_ceiling_val) as Hac.
assert (HRv : RGBA_STK = 24576) by reflexivity. assert (HFv : RGBA_FRAME = 5168) by reflexivity.
split; [exact HJ'|].
split. { assert (Hin : In (r, RGB_SIZE) (blocks L2 A2)) by (eapply Permutation_in; [apply Permutation_sym; exact HB2|]; apply in_app_iff; left; left; reflexivity).
apply blocks_In in Hin as (q & _ & Hq). exact (init_done_of_block A2 (q, RGB_SIZE) (proj1 (proj2 (proj1 HJ'))) Hq). }
split; [exact Hfrm|]. split; [exact Hra|]. split; [exact Hal|]. split; [exact Htp|].
split. { intros j rr Hj k Hk. assert (Hj13 : (j < 13)%nat) by (apply (proj1 (nth_error_Some RA_SAVED j)); congruence).
rewrite KH; [exact (HRA j rr Hj k Hk) | unfold sp0 in *; lia | unfold sp, sp0 in *; lia]. }
split; [exact Hc8|]. split; [exact Hclo|]. split; [exact Hchi|].
split. { eapply (obj_at_transport_range ubs2segs _ _ _ _ _ RGBFC_SIZE); [exact Hcfp | reflexivity |].
intros k Hk. unfold RGBFC_SIZE in *. apply KH; unfold sp, sp0 in *; lia. }
split; [exact Hro | exact HINV'].
Qed.
End e.
End d.
End c.
