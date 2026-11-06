(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.cgif.cgif_file_fuzzer.lib Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.cgif.cgif_file_fuzzer.lib Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YM06 YK0s.
From OSSVerify.Proofs.cgif.cgif_file_fuzzer.lib Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00.
From OSSVerify.Proofs.cgif.cgif_file_fuzzer.lib Require Import YN3v.
From OSSVerify.Proofs.cgif.cgif_file_fuzzer.lib Require Import YO0i YO0f YO0x YO0d YO0e.
From OSSVerify.Proofs.cgif.cgif_file_fuzzer.lib Require Import YI04 YI08 YI0t.
From OSSVerify.Proofs.cgif.cgif_file_fuzzer.lib Require Import YM05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Open Scope bv_scope.
Open Scope Z_scope.
Section f. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Section g.
Variable segs : list Segment.
Definition arr16 (mem : word -> option byte) (base : Z) (l : list Z) : Prop :=
forall j, (j < length l)%nat -> val_mem segs mem (base + 2 * Z.of_nat j) 2 (nth j l 0) /\ 0 <= nth j l 0 < 65536.
Lemma arr16_nth : forall mem base l j, arr16 mem base l -> (j < length l)%nat ->
val_mem segs mem (base + 2 * Z.of_nat j) 2 (nth j l 0) /\ 0 <= nth j l 0 < 65536.
Proof. intros mem base l j H Hj. exact (H j Hj). Qed.
Lemma arr16_nthZ : forall mem base l i, arr16 mem base l -> 0 <= i -> (Z.to_nat i < length l)%nat ->
val_mem segs mem (base + 2 * i) 2 (nth (Z.to_nat i) l 0) /\ 0 <= nth (Z.to_nat i) l 0 < 65536.
Proof. intros mem base l i H Hi Hlt. rewrite <- (Z2Nat.id i) at 1 by exact Hi. exact (H _ Hlt). Qed.
Lemma arr16_frame : forall mem mem' base l,
arr16 mem base l ->
(forall a, base <= a < base + 2 * Z.of_nat (length l) -> mbyte segs mem' a = mbyte segs mem a) ->
arr16 mem' base l.
Proof.
intros mem mem' base l H Hfr j Hj. destruct (H j Hj) as [Hv Hr]. split; [|exact Hr].
intros k Hk. rewrite Hfr; [apply Hv; exact Hk|]. lia.
Qed.
Lemma arr16_upd : forall mem mem' base l i v,
arr16 mem base l -> 0 <= i -> (Z.to_nat i < length l)%nat -> 0 <= v < 65536 ->
val_mem segs mem' (base + 2 * i) 2 v ->
(forall a, base <= a < base + 2 * Z.of_nat (length l) -> ~ (base + 2 * i <= a < base + 2 * i + 2) ->
mbyte segs mem' a = mbyte segs mem a) ->
arr16 mem' base (updn l (Z.to_nat i) v).
Proof.
intros mem mem' base l i v H Hi Hlt Hv Hval Hfr j Hj. rewrite updn_length in Hj.
rewrite nth_updn. destruct (Nat.eqb_spec j (Z.to_nat i)).
- subst j. replace (Z.to_nat i <? length l)%nat with true by (symmetry; apply Nat.ltb_lt; exact Hlt). cbn [andb].
rewrite Z2Nat.id by exact Hi. split; [exact Hval | exact Hv].
- cbn [andb]. destruct (H j Hj) as [Hv0 Hr]. split; [|exact Hr].
intros k Hk. rewrite Hfr; [apply Hv0; exact Hk | lia | lia].
Qed.
Lemma arr16_zero_range : forall mem mem' base l i n,
arr16 mem base l -> 0 <= i -> 0 <= n -> (Z.to_nat i + Z.to_nat n <= length l)%nat ->
(forall a, base + 2 * i <= a < base + 2 * i + 2 * n -> mbyte segs mem' a = Some (Z_to_bv 8 0)) ->
(forall a, base <= a < base + 2 * Z.of_nat (length l) -> ~ (base + 2 * i <= a < base + 2 * i + 2 * n) ->
mbyte segs mem' a = mbyte segs mem a) ->
arr16 mem' base (zero_range l (Z.to_nat i) (Z.to_nat n)).
Proof.
intros mem mem' base l i n H Hi Hn Hlen Hz Hfr j Hj. rewrite zero_range_length in Hj.
rewrite nth_zero_range by exact Hlen.
destruct (Nat.leb_spec (Z.to_nat i) j), (Nat.ltb_spec j (Z.to_nat i + Z.to_nat n)); cbn [andb].
1: { split; [|lia]. intros k Hk. rewrite Hz by lia. f_equal. unfold le_byte. destruct k as [|[|k]]; [reflexivity | reflexivity | lia]. }
all: destruct (H j Hj) as [Hv0 Hr]; split; [|exact Hr]; intros k Hk; rewrite Hfr; [apply Hv0; exact Hk | lia | lia].
Qed.
Lemma arr16_zeros : forall mem base n,
(forall a, base <= a < base + 2 * Z.of_nat n -> mbyte segs mem a = Some (Z_to_bv 8 0)) ->
arr16 mem base (repeat 0 n).
Proof.
intros mem base n Hz j Hj. rewrite repeat_length in Hj. rewrite nth_repeat. split; [|lia].
intros k Hk. rewrite Hz by lia. f_equal. unfold le_byte. destruct k as [|[|k]]; [reflexivity | reflexivity | lia].
Qed.
Lemma arr16_of_present : forall mem base n,
(forall a, base <= a < base + 2 * Z.of_nat n -> present mem a) ->
exists l, length l = n /\ arr16 mem base l.
Proof.
intros mem base n. revert base. induction n as [|n IH]; intros base Hp.
- exists []. split; [reflexivity|]. intros j Hj. cbn in Hj. lia.
- destruct (val_mem2 segs mem base) as (X & HX & HV); [apply Hp; lia | apply Hp; lia |].
destruct (IH (base + 2)) as (l & Hlen & Hl); [intros a Ha; apply Hp; lia|].
exists (X :: l). split; [cbn; lia|]. intros [|j] Hj.
+ cbn [nth]. rewrite Z.mul_0_r, Z.add_0_r. split; [exact HV | exact HX].
+ cbn [nth]. destruct (Hl j ltac:(cbn in Hj; lia)) as [Hv Hr]. split; [|exact Hr].
replace (base + 2 * Z.of_nat (S j)) with (base + 2 + 2 * Z.of_nat j) by lia. exact Hv.
Qed.
Definition reg16 (p k : nat) (w : bool) : YP09.region :=
YP09.mkRegion (Some p) 0 2 0 (if w then 2 else 0) [mkChunk 0 (CVal 2 (SOff k 0))].
Lemma region_ok_reg16 : forall E mem p k w a v,
ew E p = Z_to_bv 64 a -> ew E k = Z_to_bv 64 v -> 0 <= a -> a + 2 <= 2 ^ 64 -> 0 <= v < 65536 ->
val_mem segs mem a 2 v -> (w = true -> forall o, 0 <= o < 2 -> writable_at segs mem (a + o)) ->
region_ok segs E mem (reg16 p k w).
Proof.
intros E mem p k w a v Hp Hk Ha Ha2 Hv Hval Hw. unfold region_ok, reg16. cbn [r_base r_lo r_hi r_wlo r_whi r_chunks base_val].
rewrite Hp, unsigned_lit_small by lia. split; [lia|]. split; [lia|]. split.
- intros o Ho. destruct w; [apply Hw; [reflexivity | lia] | lia].
- constructor; [|constructor]. eapply chunk_ok_val; [| exact Hv | cbn; lia | rewrite Z.add_0_r; exact Hval].
cbn [sv_denot]. rewrite Hk, unsigned_lit_small by lia. rewrite Z.add_0_r. reflexivity.
Qed.
Definition reg8 (p k : nat) (w : bool) : YP09.region :=
YP09.mkRegion (Some p) 0 1 0 (if w then 1 else 0) [mkChunk 0 (CVal 1 (SOff k 0))].
Lemma region_ok_reg8 : forall E mem p k w a v,
ew E p = Z_to_bv 64 a -> ew E k = Z_to_bv 64 v -> 0 <= a -> a + 1 <= 2 ^ 64 -> 0 <= v < 256 ->
val_mem segs mem a 1 v -> (w = true -> writable_at segs mem a) ->
region_ok segs E mem (reg8 p k w).
Proof.
intros E mem p k w a v Hp Hk Ha Ha2 Hv Hval Hw. unfold region_ok, reg8. cbn [r_base r_lo r_hi r_wlo r_whi r_chunks base_val].
rewrite Hp, unsigned_lit_small by lia. split; [lia|]. split; [lia|]. split.
- intros o Ho. destruct w; [replace (a + o) with a by lia; apply Hw; reflexivity | lia].
- constructor; [|constructor]. eapply chunk_ok_val; [| exact Hv | cbn; lia | rewrite Z.add_0_r; exact Hval].
cbn [sv_denot]. rewrite Hk, unsigned_lit_small by lia. rewrite Z.add_0_r. reflexivity.
Qed.
Definition regw (p : nat) (n : Z) : YP09.region := YP09.mkRegion (Some p) 0 n 0 n [].
Lemma region_ok_regw : forall E mem p n a,
ew E p = Z_to_bv 64 a -> 0 <= a < 2 ^ 64 -> a + n <= 2 ^ 64 -> 0 <= n ->
(forall o, 0 <= o < n -> writable_at segs mem (a + o)) ->
region_ok segs E mem (regw p n).
Proof.
intros E mem p n a Hp Ha Han Hn Hw. unfold region_ok, regw. cbn [r_base r_lo r_hi r_wlo r_whi r_chunks base_val].
rewrite Hp, unsigned_lit_small by lia. split; [lia|]. split; [lia|]. split; [|constructor]. intros o Ho. apply Hw. exact Ho.
Qed.
Lemma val_mem_of_region16 : forall E mem r p a e v,
region_ok segs E mem r -> r_base r = Some p -> In (mkChunk 0 (CVal 2 e)) (r_chunks r) ->
bv_unsigned (ew E p) = a -> sv_denot E e = Z_to_bv 64 v -> 0 <= v < 65536 ->
val_mem segs mem a 2 v.
Proof.
intros E mem r p a e v HR Hb Hin Hp He Hv.
destruct HR as (_ & _ & _ & Hcs). pose proof (proj1 (Forall_forall _ _) Hcs _ Hin) as Hc.
rewrite Hb in Hc. cbn [base_val] in Hc. rewrite Hp in Hc.
rewrite <- (Z.add_0_r a). change 2%nat with (N.to_nat 2).
eapply val_of_chunk_ok; [exact Hc | exact He | cbn; lia | cbn; lia].
Qed.
End g.
Section J.
Variable B : malloc_syms.
Variable MR : MR_t.
Hypothesis LAWS : MR_laws B MR.
Hypothesis errno_low : errno_addr B + 4 <= alloc_ceiling.
Hypothesis IMG : img_laws B MR.
Variable tbl : ctable.
Hypothesis tbl_ok : table_ok (ms_segs B) tbl.
Local Notation segs := (ms_segs B).
Lemma wr_ok_cons_win : forall E r rs STK sp0 FP bl0 blc n b,
r_base r = Some n -> bv_unsigned (ew E n) = b ->
(r_wlo r < r_whi r -> sp0 - STK <= b + r_wlo r /\ b + r_whi r <= sp0) ->
wr_ok E rs STK sp0 FP bl0 blc -> wr_ok E (r :: rs) STK sp0 FP bl0 blc.
Proof.
intros E r rs STK sp0 FP bl0 blc n b Hb Hn Hw H a (r' & [<-|Hin] & Ha).
- left. rewrite Hb in Ha. cbn [base_val] in Ha. rewrite Hn in Ha. specialize (Hw ltac:(lia)). lia.
- apply H. exists r'. auto.
Qed.
Lemma journal_sub_gen : forall STK sp0 FP L A mem md Lc Ac memc mdc STK1 sp1 FP1 L2 A2 mem2 md2,
journal B MR STK sp0 FP L A mem md Lc Ac memc mdc ->
journal B MR STK1 sp1 FP1 Lc Ac memc mdc L2 A2 mem2 md2 ->
sp0 - STK <= sp1 - STK1 -> sp1 <= sp0 ->
(forall a, inFP FP1 a -> (inFP FP a /\ a < alloc_ceiling) \/
(exists b n, In (b, n) (blocks Lc Ac) /\ ~ In (b, n) (blocks L A) /\ b <= a < b + n)) ->
journal B MR STK sp0 FP L A mem md L2 A2 mem2 md2.
Proof.
intros STK sp0 FP L A mem md Lc Ac memc mdc STK1 sp1 FP1 L2 A2 mem2 md2
(HH & Hvm & Hhigh & Hblk & Hgone & Hst & Herr & Himg)
(HH2 & Hvm2 & Hhigh2 & Hblk2 & Hgone2 & Hst2 & Herr2 & Himg2) Hlo Hhi HF.
pose proof (proj1 alloc_ceiling_val) as Hac.
destruct Hst as (Hal & Hstk0 & Hceil & H63 & Hstw). destruct Hst2 as (Hal2 & Hstk2 & Hceil2 & H632 & Hstw2).
assert (HF' : forall a n i, In (a, n) (blocks L A) -> In (a, n) (blocks Lc Ac) -> 0 <= i < n ->
inFP FP1 (a + i) -> inFP FP (a + i)).
{ intros a n i H0 Hc Hi Hf. destruct (HF _ Hf) as [[H _] | (b & m & Hbin & Hbn & Hr)]; [exact H|].
exfalso. assert (Hne : (b, m) <> (a, n)) by (intros E; rewrite E in Hbn; exact (Hbn H0)).
destruct (heap_sep_in2 B MR LAWS Lc Ac memc mdc (b, m) (a, n) HH Hbin Hc Hne) as [Hd|Hd]; cbn [fst snd] in Hd; lia. }
split; [exact HH2|]. split.
{ destruct Hvm2 as [vm2 ->]. destruct Hvm as [vm ->]. exists vm2. apply with_vmmaps_twice. }
split.
{ intros a Ha Hna. destruct (Hhigh2 a Ha ltac:(lia)) as [E1 E2]. destruct (Hhigh a Ha Hna) as [F1 F2].
split; [rewrite E1; exact F1 | rewrite F2; exact E2]. }
split.
{ intros a n i H1 H2 Hi Hnf.
destruct (in_dec zz_eq_dec (a, n) (blocks Lc Ac)) as [Hc|Hc].
- rewrite <- (Hblk a n i H1 Hc Hi Hnf). apply (Hblk2 a n i Hc H2 Hi).
intros Hf. exact (Hnf (HF' a n i H1 Hc Hi Hf)).
- exfalso. exact (Hnf (Hgone a n i H1 Hc Hi)). }
split.
{ intros a n i H1 H2 Hi.
destruct (in_dec zz_eq_dec (a, n) (blocks Lc Ac)) as [Hc|Hc]; [|exact (Hgone a n i H1 Hc Hi)].
apply (HF' a n i H1 Hc Hi). exact (Hgone2 a n i Hc H2 Hi). }
split.
{ split; [exact Hal|]. split; [exact Hstk0|]. split; [exact Hceil|]. split; [exact H63|].
intros a Ha. destruct (Z_lt_le_dec a (sp1 - STK1)) as [Hb|Hb].
- apply (proj1 (proj2 (Hhigh2 a ltac:(lia) ltac:(lia)))). apply Hstw. exact Ha.
- destruct (Z_lt_le_dec a sp1) as [Hb2|Hb2].
+ apply Hstw2. lia.
+ apply (proj1 (proj2 (Hhigh2 a ltac:(lia) ltac:(lia)))). apply Hstw. exact Ha. }
split; [exact Herr2 | eapply img_kept_trans; [exact Himg | exact Himg2]].
Qed.
Definition memset_spec (pcm : Z) : Prop :=
forall (d c nw : word) (n : nat) (mem rom : word -> option byte) (regs : bvmap 5 word),
getr regs 10 = d -> getr regs 11 = c -> getr regs 12 = nw ->
bv_unsigned nw = Z.of_nat n ->
store_ok segs mem d n = true ->
bv_unsigned d + Z.of_nat n <= 2 ^ 64 ->
exists regs',
msteps segs (mkst regs (Z_to_bv 64 pcm) mem rom)
(mkst regs' (v_jalr (getr regs 1) 0) (wbytes mem d (repeat (Z_to_bv 8 (bv_unsigned c mod 256)) n)) rom)
/\ getr regs' 10 = d
/\ (forall r : reg, r <> 11%bv -> r <> 12%bv -> r <> 13%bv -> r <> 14%bv -> r <> 15%bv -> r <> 16%bv ->
getr regs' r = getr regs r).
Definition MEMSET_CLOB : list reg := [11; 12; 13; 14; 15; 16]%bv.
Lemma memset_clob_out : forall r : reg, reg_in r MEMSET_CLOB = false ->
r <> 11%bv /\ r <> 12%bv /\ r <> 13%bv /\ r <> 14%bv /\ r <> 15%bv /\ r <> 16%bv.
Proof. intros r Hr. repeat split; intros ->; vm_compute in Hr; discriminate. Qed.
Lemma jmemset : forall pcm, memset_spec pcm ->
forall E ss ms STK sp0 FP L A mem md Lc Ac mdc d c n raw,
st_ok segs E ss ms -> ss_pc ss = pcm -> ss_resv ss = None ->
journal B MR STK sp0 FP L A mem md Lc Ac (ms_mem ms) mdc ->
getr (ms_regs ms) 10 = Z_to_bv 64 d -> getr (ms_regs ms) 11 = Z_to_bv 64 c -> getr (ms_regs ms) 12 = Z_to_bv 64 n ->
getr (ms_regs ms) 1 = raw -> YK0s.ret_ok raw ->
0 <= n -> 0 <= d -> d + n < 2 ^ 64 -> 0 <= c < 256 ->
(forall i, 0 <= i < n -> present (ms_mem ms) (d + i)) ->
(forall a, d <= a < d + n -> wr_byte STK sp0 FP (blocks L A) (blocks Lc Ac) a) ->
SR segs (mkCfg ms mdc)
(fun c' => exists regs2 mem2,
c' = mkCfg (mkst regs2 raw mem2 (seg_rom segs)) mdc /\
journal B MR STK sp0 FP L A mem md Lc Ac mem2 mdc /\
getr regs2 10 = Z_to_bv 64 d /\
(forall r, reg_in r MEMSET_CLOB = false -> getr regs2 r = getr (ms_regs ms) r) /\
(forall x : word, bv_unsigned x < d \/ d + n <= bv_unsigned x -> mem2 x = ms_mem ms x) /\
mem_grows (ms_mem ms) mem2 /\
(forall i, 0 <= i < n -> mbyte segs mem2 (d + i) = Some (Z_to_bv 8 c))).
Proof.
intros pcm HM E ss ms STK sp0 FP L A mem md Lc Ac mdc d c n raw HS Hpc Hrv HJ H10 H11 H12 H1 Hraw
Hn Hd Hdn Hc Hpd HW.
pose proof (store_ok_of_present B (ms_mem ms) (Z.to_nat n) d ltac:(intros i Hi; apply Hpd; lia) Hd ltac:(lia)) as Hst.
destruct (HM (Z_to_bv 64 d) (Z_to_bv 64 c) (Z_to_bv 64 n) (Z.to_nat n) (ms_mem ms) (seg_rom segs) (ms_regs ms) H10 H11 H12)
as (regs2 & Hms & Ha0 & Hfr).
{ rewrite unsigned_lit_small by lia. lia. }
{ exact Hst. }
{ rewrite unsigned_lit_small by lia. lia. }
rewrite (st_ok_mkst segs E ss ms HS Hrv), Hpc.
destruct (heap_model B MR LAWS _ _ _ _ (proj1 HJ)) as (Hh & Hl & _).
eapply SR_msteps; [exact Hh | exact Hl | exact Hms |].
set (bs := repeat (Z_to_bv 8 (bv_unsigned (Z_to_bv 64 c) mod 256)) (Z.to_nat n)).
assert (Hlen : length bs = Z.to_nat n) by (subst bs; apply repeat_length).
apply SR_ret. exists regs2, (wbytes (ms_mem ms) (Z_to_bv 64 d) bs). rewrite H1, Hraw.
assert (Hout : forall x : word, bv_unsigned x < d \/ d + n <= bv_unsigned x -> wbytes (ms_mem ms) (Z_to_bv 64 d) bs x = ms_mem ms x).
{ intros x Hx. destruct Hx as [Hx|Hx].
- apply wbytes_below; rewrite ?Hlen, unsigned_lit_small by lia; lia.
- apply wbytes_above. rewrite Hlen, unsigned_lit_small by lia. lia. }
split; [reflexivity|]. split.
{ eapply (journal_exec B MR LAWS IMG) with (W := fun a => d <= a < d + n); [exact HJ | | apply wbytes_grows | exact HW].
intros x Hx. apply Hout. lia. }
split; [exact Ha0|]. split.
{ intros r Hr. destruct (memset_clob_out r Hr) as (?&?&?&?&?&?). apply Hfr; assumption. }
split; [exact Hout|]. split; [apply wbytes_grows|].
intros i Hi. rewrite (wbytes_mbyte segs bs (ms_mem ms) d (d + i)) by (rewrite ?Hlen; lia).
rewrite ?Hlen.
replace ((d <=? d + i) && (d + i <? d + Z.of_nat (Z.to_nat n))) with true.
2:{ symmetry. apply andb_true_intro. split; [apply Z.leb_le | apply Z.ltb_lt]; lia. }
subst bs. rewrite nth_error_repeat by lia. f_equal. f_equal.
rewrite unsigned_lit_small by lia. apply Z.mod_small. lia.
Qed.
Lemma jmalloc_at : malloc_realizes B MR ->
forall E ss ms STK sp0 FP L A mem md Lc Ac mdc n spc raw,
st_ok segs E ss ms -> ss_pc ss = ms_malloc B -> ss_resv ss = None ->
journal B MR STK sp0 FP L A mem md Lc Ac (ms_mem ms) mdc ->
st_init_done Ac = true ->
getr (ms_regs ms) 10 = Z_to_bv 64 n -> 0 <= n < 2 ^ 62 ->
getr (ms_regs ms) 2 = Z_to_bv 64 spc -> 0 <= spc < 2 ^ 64 -> spc mod 16 = 0 ->
sp0 - STK <= spc - ALLOC_STACK -> spc <= sp0 ->
getr (ms_regs ms) 4 = Z_to_bv 64 (ms_tp B) ->
getr (ms_regs ms) 1 = raw -> YK0s.ret_ok raw ->
SR segs (mkCfg ms mdc)
(fun c' => exists L2 A2 regs2 mem2 md2 (res : Z),
c' = mkCfg (mkst regs2 raw mem2 (seg_rom segs)) md2 /\
journal B MR STK sp0 FP L A mem md L2 A2 mem2 md2 /\
st_init_done A2 = true /\
regs_preserved (ms_regs ms) regs2 /\
getr regs2 10 = Z_to_bv 64 res /\
((res = 0 /\ blocks L2 A2 = blocks Lc Ac)
\/ (res <> 0 /\ res mod 16 = 0 /\
(exists b1 b2, blocks L2 A2 = b1 ++ (res, n) :: b2 /\ blocks Lc Ac = b1 ++ b2) /\
(forall blc i, In (res, n) blc -> 0 <= i < n -> wr_byte STK sp0 FP (blocks L A) blc (res + i)))) /\
(forall b m i, In (b, m) (blocks Lc Ac) -> 0 <= i < m ->
mbyte segs mem2 (b + i) = mbyte segs (ms_mem ms) (b + i)) /\
(forall x, alloc_ceiling <= x < 2 ^ 64 -> ~ (spc - ALLOC_STACK <= x < spc) ->
mbyte segs mem2 x = mbyte segs (ms_mem ms) x /\
(writable_at segs (ms_mem ms) x <-> writable_at segs mem2 x))).
Proof.
intros HMA E ss ms STK sp0 FP L A mem md Lc Ac mdc n spc raw
HS Hpc Hrv HJ Hid Ha0 Hn Hsp Hspc Hal Hlo Hhi Htp Hra Hraw.
assert (Hsp' : spZ (ms_regs ms) = spc).
{ unfold spZ. rewrite Hsp. apply unsigned_lit_small. exact Hspc. }
rewrite (st_ok_mkst segs E ss ms HS Hrv), Hpc.
eapply SR_mono.
{ eapply (cg_malloc B MR LAWS errno_low IMG HMA STK sp0 FP L A mem md Lc Ac (ms_regs ms) (ms_mem ms) mdc n HJ Hid Ha0 Hn).
- rewrite Hra. exact Hraw.
- rewrite Hsp'. exact Hal.
- rewrite Hsp'. exact Hlo.
- rewrite Hsp'. exact Hhi.
- exact Htp. }
intros c' (L2 & A2 & regs2 & mem2 & md2 & res & -> & HJ2 & Hid2 & HP2 & Hr10 & Hres & Hkeep & Hhi2).
exists L2, A2, regs2, mem2, md2, res. rewrite Hra. split; [reflexivity|]. split; [exact HJ2|]. split; [exact Hid2|].
split; [exact HP2|]. split; [exact Hr10|]. split; [exact Hres|]. split; [exact Hkeep|].
intros x Hx Hnx. apply Hhi2; [exact Hx|]. rewrite Hsp'. exact Hnx.
Qed.
Lemma jfree_at : free_realizes B MR ->
forall E ss ms STK sp0 FP L A mem md Lc Ac mdc a n spc raw,
st_ok segs E ss ms -> ss_pc ss = ms_free B -> ss_resv ss = None ->
journal B MR STK sp0 FP L A mem md Lc Ac (ms_mem ms) mdc ->
In (a, n) (blocks Lc Ac) ->
getr (ms_regs ms) 10 = Z_to_bv 64 a ->
getr (ms_regs ms) 2 = Z_to_bv 64 spc -> 0 <= spc < 2 ^ 64 -> spc mod 16 = 0 ->
sp0 - STK <= spc - ALLOC_STACK -> spc <= sp0 ->
getr (ms_regs ms) 4 = Z_to_bv 64 (ms_tp B) ->
getr (ms_regs ms) 1 = raw -> YK0s.ret_ok raw ->
(In (a, n) (blocks L A) -> forall i, 0 <= i < n -> inFP FP (a + i)) ->
SR segs (mkCfg ms mdc)
(fun c' => exists L2 A2 regs2 mem2 md2,
c' = mkCfg (mkst regs2 raw mem2 (seg_rom segs)) md2 /\
journal B MR STK sp0 FP L A mem md L2 A2 mem2 md2 /\
regs_preserved (ms_regs ms) regs2 /\
rm1 (a, n) (blocks Lc Ac) (blocks L2 A2) /\
(forall b m i, In (b, m) (blocks L2 A2) -> 0 <= i < m ->
mbyte segs mem2 (b + i) = mbyte segs (ms_mem ms) (b + i)) /\
(forall x, alloc_ceiling <= x < 2 ^ 64 -> ~ (spc - ALLOC_STACK <= x < spc) ->
mbyte segs mem2 x = mbyte segs (ms_mem ms) x /\
(writable_at segs (ms_mem ms) x <-> writable_at segs mem2 x)) /\
st_init_done A2 = true).
Proof.
intros HFR E ss ms STK sp0 FP L A mem md Lc Ac mdc a n spc raw
HS Hpc Hrv HJ Hin Ha0 Hsp Hspc Hal Hlo Hhi Htp Hra Hraw HFP.
assert (Hsp' : spZ (ms_regs ms) = spc).
{ unfold spZ. rewrite Hsp. apply unsigned_lit_small. exact Hspc. }
rewrite (st_ok_mkst segs E ss ms HS Hrv), Hpc.
apply blocks_In in Hin as (p & Hp & Hpin).
eapply SR_mono.
{ eapply (cg_free B MR LAWS errno_low IMG HFR STK sp0 FP L A mem md Lc Ac (ms_regs ms) (ms_mem ms) mdc p n HJ Hpin).
- rewrite Hp. exact Ha0.
- rewrite Hra. exact Hraw.
- rewrite Hsp'. exact Hal.
- rewrite Hsp'. exact Hlo.
- rewrite Hsp'. exact Hhi.
- exact Htp.
- rewrite Hp. exact HFP. }
intros c' (L2 & A2 & regs2 & mem2 & md2 & -> & HJ2 & HP2 & Hrm & Hkeep & Hhi2 & Hid2).
exists L2, A2, regs2, mem2, md2. rewrite Hra. split; [reflexivity|]. split; [exact HJ2|]. split; [exact HP2|].
rewrite Hp in Hrm. split; [exact Hrm|]. split; [exact Hkeep|]. split; [|exact Hid2].
intros x Hx Hnx. apply Hhi2; [exact Hx|]. rewrite Hsp'. exact Hnx.
Qed.
Lemma jfree_opt : free_realizes B MR -> free_null_realizes B ->
forall E ss ms STK sp0 FP L A mem md Lc Ac mdc a n spc raw,
st_ok segs E ss ms -> ss_pc ss = ms_free B -> ss_resv ss = None ->
journal B MR STK sp0 FP L A mem md Lc Ac (ms_mem ms) mdc ->
(a = 0 \/ (In (a, n) (blocks Lc Ac) /\ ~ In (a, n) (blocks L A))) ->
getr (ms_regs ms) 10 = Z_to_bv 64 a ->
getr (ms_regs ms) 2 = Z_to_bv 64 spc -> 0 <= spc < 2 ^ 64 -> spc mod 16 = 0 ->
sp0 - STK <= spc - ALLOC_STACK -> spc <= sp0 ->
getr (ms_regs ms) 4 = Z_to_bv 64 (ms_tp B) ->
getr (ms_regs ms) 1 = raw -> YK0s.ret_ok raw ->
SR segs (mkCfg ms mdc)
(fun c' => exists L2 A2 regs2 mem2 md2,
c' = mkCfg (mkst regs2 raw mem2 (seg_rom segs)) md2 /\
journal B MR STK sp0 FP L A mem md L2 A2 mem2 md2 /\
regs_preserved (ms_regs ms) regs2 /\
(a = 0 /\ blocks L2 A2 = blocks Lc Ac \/ a <> 0 /\ rm1 (a, n) (blocks Lc Ac) (blocks L2 A2)) /\
(forall b m i, In (b, m) (blocks L2 A2) -> 0 <= i < m ->
mbyte segs mem2 (b + i) = mbyte segs (ms_mem ms) (b + i)) /\
(forall x, alloc_ceiling <= x < 2 ^ 64 -> ~ (spc - ALLOC_STACK <= x < spc) ->
mbyte segs mem2 x = mbyte segs (ms_mem ms) x /\
(writable_at segs (ms_mem ms) x <-> writable_at segs mem2 x))).
Proof.
intros HFR HFN E ss ms STK sp0 FP L A mem md Lc Ac mdc a n spc raw
HS Hpc Hrv HJ Ha Ha0 Hsp Hspc Hal Hlo Hhi Htp Hra Hraw.
destruct (Z.eq_dec a 0) as [Hz | Hnz].
- subst a. destruct (heap_model B MR LAWS _ _ _ _ (proj1 HJ)) as (Hh & Hl & _).
eapply SR_mono; [eapply (jfree_null B HFN); try eassumption|].
intros c' ->. exists Lc, Ac, (ms_regs ms), (ms_mem ms), mdc.
split; [reflexivity|]. split; [exact HJ|]. split; [intros r Hr; reflexivity|].
split; [left; split; reflexivity|]. split; [intros; reflexivity|]. intros x _ _. split; [reflexivity | tauto].
- destruct Ha as [Hz | [Hin Hnot]]; [lia|].
eapply SR_mono; [eapply (jfree_at HFR); try eassumption; intros H0; exfalso; exact (Hnot H0)|].
intros c' (L2 & A2 & regs2 & mem2 & md2 & -> & HJ2 & HP2 & Hrm & Hkeep & Hhi2 & _).
exists L2, A2, regs2, mem2, md2. split; [reflexivity|]. split; [exact HJ2|]. split; [exact HP2|].
split; [right; split; [exact Hnz | exact Hrm]|]. split; [exact Hkeep | exact Hhi2].
Qed.
Lemma journal_stack_w : forall STK sp0 FP L A mem md L' A' mem' md',
journal B MR STK sp0 FP L A mem md L' A' mem' md' -> forall a, sp0 - STK <= a < sp0 -> writable_at segs mem' a.
Proof. intros STK sp0 FP L A mem md L' A' mem' md' (_ & _ & _ & _ & _ & (_ & _ & _ & _ & Hw) & _) a Ha. apply Hw. exact Ha. Qed.
Lemma journal_heap : forall STK sp0 FP L A mem md L' A' mem' md',
journal B MR STK sp0 FP L A mem md L' A' mem' md' -> heap_ok MR L' A' mem' md'.
Proof. intros STK sp0 FP L A mem md L' A' mem' md' (HH & _). exact HH. Qed.
Lemma journal_mem_eq : forall STK sp0 FP L A mem md L' A' mem1 mem2 md',
journal B MR STK sp0 FP L A mem md L' A' mem1 md' -> (forall x, mem2 x = mem1 x) ->
journal B MR STK sp0 FP L A mem md L' A' mem2 md'.
Proof.
intros STK sp0 FP L A mem md L' A' mem1 mem2 md' HJ Heq.
eapply (journal_exec B MR LAWS IMG) with (W := fun _ => False); [exact HJ | intros x _; apply Heq | | intros a F; destruct F].
intros x Hx. rewrite Heq. exact Hx.
Qed.
End J.
Section h.
Variable E : env.
Lemma swrap32_small : forall x, 0 <= x < 2 ^ 31 -> bv_swrap 32 x = x.
Proof.
intros x Hx. unfold bv_swrap, bv_wrap. change (bv_half_modulus 32) with (2 ^ 31). change (bv_modulus 32) with (2 ^ 32).
rewrite Z.mod_small by lia. lia.
Qed.
Lemma wrap64_small : forall x, 0 <= x < 2 ^ 64 -> bv_wrap 64 x = x.
Proof. intros x Hx. unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64). apply Z.mod_small. lia. Qed.
Lemma alias_b2i : forall nb ni nk base i,
ew E nb = Z_to_bv 64 base -> ew E ni = Z_to_bv 64 i -> ew E nk = Z_to_bv 64 (base + 2 * i) ->
0 <= base -> 0 <= i -> base + 2 * i < 2 ^ 64 ->
sv_denot E (SAlu ALU_ADD (SAlu ALU_SLL (SOff ni 0) (SLit 1)) (SOff nb 0)) = sv_denot E (SOff nk 0).
Proof.
intros nb ni nk base i Hb Hi Hk H0 H1 H2. apply U_inj.
rewrite !U_SAlu. cbn [zalu_raw]. rewrite U_SLit. change (Z.land (zcanon 1) 63) with 1.
rewrite (U_atom E ni i Hi), (U_atom E nb base Hb), (U_atom E nk (base + 2 * i) Hk) by lia.
rewrite Z.shiftl_mul_pow2 by lia. change (2 ^ 1) with 2.
rewrite (zcanon_id (i * 2)) by (unfold M64; lia). rewrite zcanon_id by (unfold M64; lia). lia.
Qed.
Lemma alias_b2i' : forall nb ni nk base i,
ew E nb = Z_to_bv 64 base -> ew E ni = Z_to_bv 64 i -> ew E nk = Z_to_bv 64 (base + 2 * i) ->
0 <= base -> 0 <= i -> base + 2 * i < 2 ^ 64 ->
sv_denot E (SAlu ALU_ADD (SOff nb 0) (SAlu ALU_SLL (SOff ni 0) (SLit 1))) = sv_denot E (SOff nk 0).
Proof.
intros nb ni nk base i Hb Hi Hk H0 H1 H2. apply U_inj.
rewrite !U_SAlu. cbn [zalu_raw]. rewrite U_SLit. change (Z.land (zcanon 1) 63) with 1.
rewrite (U_atom E ni i Hi), (U_atom E nb base Hb), (U_atom E nk (base + 2 * i) Hk) by lia.
rewrite Z.shiftl_mul_pow2 by lia. change (2 ^ 1) with 2.
rewrite (zcanon_id (i * 2)) by (unfold M64; lia). rewrite zcanon_id by (unfold M64; lia). lia.
Qed.
Lemma alias_add : forall na nb nk a b,
ew E na = Z_to_bv 64 a -> ew E nb = Z_to_bv 64 b -> ew E nk = Z_to_bv 64 (a + b) ->
0 <= a -> 0 <= b -> a + b < 2 ^ 64 ->
sv_denot E (SAlu ALU_ADD (SOff na 0) (SOff nb 0)) = sv_denot E (SOff nk 0).
Proof.
intros na nb nk a b Ha Hb Hk H0 H1 H2. apply U_inj.
rewrite U_SAlu. cbn [zalu_raw]. rewrite (U_atom E na a Ha), (U_atom E nb b Hb), (U_atom E nk (a + b) Hk) by lia.
rewrite zcanon_id by (unfold M64; lia). lia.
Qed.
Lemma alias_tmrow : forall nm nd nc nk m idl c,
ew E nm = Z_to_bv 64 m -> ew E nd = Z_to_bv 64 idl -> ew E nc = Z_to_bv 64 c -> ew E nk = Z_to_bv 64 (2 * ((m - 1) * idl + c)) ->
1 <= m < 2 ^ 16 -> 0 <= idl <= 256 -> 0 <= c < 256 -> (m - 1) * idl + c < 2 ^ 30 ->
sv_denot E (SAlu ALU_SLL (SAluw ALU_ADD (SMd M_MUL (SOff nm (-1)) (SOff nd 0)) (SOff nc 0)) (SLit 1)) = sv_denot E (SOff nk 0).
Proof.
intros nm nd nc nk m idl c Hm Hd Hc Hk Rm Rd Rc Rk.
assert (Hprod : 0 <= (m - 1) * idl) by (apply Z.mul_nonneg_nonneg; lia).
apply U_inj. rewrite U_SAlu. cbn [zalu_raw]. rewrite U_SLit. change (Z.land (zcanon 1) 63) with 1.
rewrite (U_of_S E (SAluw _ _ _)), S_SAluw. cbn [zalu_raw].
rewrite U_SMd. cbn [zmd_raw]. rewrite (U_atom_off E nm m (-1) Hm), (U_atom E nd idl Hd), (U_atom E nc c Hc) by lia.
rewrite (U_atom E nk _ Hk) by lia.
rewrite (zcanon_id ((m + -1) * idl)) by (unfold M64; lia).
replace ((m + -1) * idl) with ((m - 1) * idl) by lia.
rewrite (Z.mod_small ((m - 1) * idl)) by lia. rewrite (Z.mod_small c) by lia.
rewrite swrap32_small by lia. rewrite (wrap64_small ((m - 1) * idl + c)) by lia.
rewrite Z.shiftl_mul_pow2 by lia. change (2 ^ 1) with 2. rewrite zcanon_id by (unfold M64; lia). lia.
Qed.
End h.
Section q.
Variable E : env.
Lemma cond_ltu : forall na ca nb cb a b,
ew E na = Z_to_bv 64 a -> ew E nb = Z_to_bv 64 b ->
0 <= a -> 0 <= a + ca -> a + ca < 2 ^ 64 -> a < 2 ^ 64 -> 0 <= b -> 0 <= b + cb -> b + cb < 2 ^ 64 -> b < 2 ^ 64 ->
a + ca < b + cb ->
acond_ok E (mkAC BC_LTU (SOff na ca) (SOff nb cb)).
Proof.
intros na ca nb cb a b Ha Hb H1 H2 H3 H4 H5 H6 H7 H8 Hlt. unfold acond_ok. cbn [ac_c ac_a ac_b].
rewrite branch_ltu_U, (U_atom_off E na a ca Ha), (U_atom_off E nb b cb Hb) by lia. apply Z.ltb_lt. exact Hlt.
Qed.
Lemma cond_geu : forall na ca nb cb a b,
ew E na = Z_to_bv 64 a -> ew E nb = Z_to_bv 64 b ->
0 <= a -> 0 <= a + ca -> a + ca < 2 ^ 64 -> a < 2 ^ 64 -> 0 <= b -> 0 <= b + cb -> b + cb < 2 ^ 64 -> b < 2 ^ 64 ->
b + cb <= a + ca ->
acond_ok E (mkAC BC_GEU (SOff na ca) (SOff nb cb)).
Proof.
intros na ca nb cb a b Ha Hb H1 H2 H3 H4 H5 H6 H7 H8 Hle. unfold acond_ok. cbn [ac_c ac_a ac_b].
rewrite branch_geu_U, (U_atom_off E na a ca Ha), (U_atom_off E nb b cb Hb) by lia.
apply Bool.negb_true_iff. apply Z.ltb_ge. exact Hle.
Qed.
Lemma cond_eq_lit : forall na a z,
ew E na = Z_to_bv 64 a -> 0 <= a < 2 ^ 64 -> 0 <= z < 2 ^ 64 -> a = z ->
acond_ok E (mkAC BC_EQ (SOff na 0) (SLit z)).
Proof.
intros na a z Ha Hr Hz Heq. unfold acond_ok. cbn [ac_c ac_a ac_b].
rewrite branch_eq_U, (U_atom E na a Ha), U_lit by lia. apply Z.eqb_eq. exact Heq.
Qed.
Lemma cond_ne_lit : forall na a z,
ew E na = Z_to_bv 64 a -> 0 <= a < 2 ^ 64 -> 0 <= z < 2 ^ 64 -> a <> z ->
acond_ok E (mkAC BC_NE (SOff na 0) (SLit z)).
Proof.
intros na a z Ha Hr Hz Hne. unfold acond_ok. cbn [ac_c ac_a ac_b].
rewrite branch_ne_U, (U_atom E na a Ha), U_lit by lia. apply Bool.negb_true_iff. apply Z.eqb_neq. exact Hne.
Qed.
Lemma alias_mul_add : forall n1 nd n2 nk c1 idl c2,
ew E n1 = Z_to_bv 64 c1 -> ew E nd = Z_to_bv 64 idl -> ew E n2 = Z_to_bv 64 c2 -> ew E nk = Z_to_bv 64 (c1 * idl + c2) ->
0 <= c1 < 2048 -> 0 <= idl <= 256 -> 0 <= c2 < 256 ->
sv_denot E (SAlu ALU_ADD (SMd M_MUL (SOff n1 0) (SOff nd 0)) (SOff n2 0)) = sv_denot E (SOff nk 0).
Proof.
intros n1 nd n2 nk c1 idl c2 H1 Hd H2 Hk R1 Rd R2.
assert (Hp : 0 <= c1 * idl <= 2047 * 256) by (split; [apply Z.mul_nonneg_nonneg; lia | apply Z.mul_le_mono_nonneg; lia]).
apply U_inj. rewrite U_SAlu. cbn [zalu_raw]. rewrite U_SMd. cbn [zmd_raw].
rewrite (U_atom E n1 c1 H1), (U_atom E nd idl Hd), (U_atom E n2 c2 H2), (U_atom E nk _ Hk) by lia.
rewrite (zcanon_id (c1 * idl)) by (unfold M64; lia). rewrite zcanon_id by (unfold M64; lia). lia.
Qed.
Lemma alias_dpfull : forall nd dp,
ew E nd = Z_to_bv 64 dp -> 0 <= dp <= 4096 ->
sv_denot E (SAlu ALU_SRL (SAlu ALU_SLL (SOff nd 0) (SLit 48)) (SLit 60)) = sv_denot E (SLit (if dp =? 4096 then 1 else 0)).
Proof.
intros nd dp Hd Hr. apply U_inj. rewrite !U_SAlu. cbn [zalu_raw]. rewrite !U_SLit.
change (Z.land (zcanon 48) 63) with 48. change (Z.land (zcanon 60) 63) with 60.
rewrite (U_atom E nd dp Hd) by lia.
rewrite Z.shiftl_mul_pow2, Z.shiftr_div_pow2 by lia.
rewrite (zcanon_id (dp * 2 ^ 48)) by (unfold M64; split; [|change (2 ^ 64) with (65536 * 2 ^ 48)]; nia).
destruct (Z.eqb_spec dp 4096) as [->|Hne].
- reflexivity.
- rewrite Z.div_small; [reflexivity|]. change (2 ^ 60) with (4096 * 2 ^ 48). nia.
Qed.
End q.
Section s.
Variable E : env.
Lemma U_addoff_mulm1 : forall na ca nb a b,
ew E na = Z_to_bv 64 a -> ew E nb = Z_to_bv 64 b ->
0 <= a < 2 ^ 64 -> 0 <= a + ca < 2 ^ 64 -> 0 <= b <= a + ca ->
U E (SAlu ALU_ADD (SOff na ca) (SMd M_MUL (SOff nb 0) (SLit (-1)))) = a + ca - b.
Proof.
intros na ca nb a b Ha Hb Ra Rca Rb.
rewrite U_SAlu. cbn [zalu_raw]. rewrite U_SMd. cbn [zmd_raw]. rewrite U_SLit.
rewrite (U_atom_off E na a ca Ha), (U_atom E nb b Hb) by lia.
change (zcanon (-1)) with (2 ^ 64 - 1).
unfold zcanon, M64. rewrite Zplus_mod_idemp_r.
replace (a + ca + b * (2 ^ 64 - 1)) with ((a + ca - b) + b * 2 ^ 64) by lia.
rewrite Z_mod_plus_full. apply Z.mod_small. lia.
Qed.
Lemma denot_addoff_mulm1 : forall na ca nb a b,
ew E na = Z_to_bv 64 a -> ew E nb = Z_to_bv 64 b ->
0 <= a < 2 ^ 64 -> 0 <= a + ca < 2 ^ 64 -> 0 <= b <= a + ca ->
sv_denot E (SAlu ALU_ADD (SOff na ca) (SMd M_MUL (SOff nb 0) (SLit (-1)))) = Z_to_bv 64 (a + ca - b).
Proof. intros. rewrite denot_lit_U, (U_addoff_mulm1 na ca nb a b) by assumption. reflexivity. Qed.
End s.
Section t.
Variable E : env.
Lemma U_mulw_row : forall nm nd m idl,
ew E nm = Z_to_bv 64 m -> ew E nd = Z_to_bv 64 idl -> 1 <= m <= 2048 -> 0 <= idl <= 256 ->
U E (SMdw M_MUL (SOff nm (-1)) (SOff nd 0)) = (m - 1) * idl.
Proof.
intros nm nd m idl Hm Hd Rm Rd.
assert (Hp : 0 <= (m - 1) * idl <= 2047 * 256) by (split; [apply Z.mul_nonneg_nonneg; lia | apply Z.mul_le_mono_nonneg; lia]).
rewrite U_of_S, S_SMdw. cbn [zmd_raw]. rewrite (U_atom_off E nm m (-1) Hm), (U_atom E nd idl Hd) by lia.
replace (m + -1) with (m - 1) by lia. rewrite (Z.mod_small ((m - 1))) by lia. rewrite (Z.mod_small idl) by lia.
rewrite swrap32_small by lia. apply wrap64_small. lia.
Qed.
Lemma denot_mulw_row : forall nm nd m idl,
ew E nm = Z_to_bv 64 m -> ew E nd = Z_to_bv 64 idl -> 1 <= m <= 2048 -> 0 <= idl <= 256 ->
sv_denot E (SMdw M_MUL (SOff nm (-1)) (SOff nd 0)) = Z_to_bv 64 ((m - 1) * idl).
Proof. intros. rewrite denot_lit_U, (U_mulw_row nm nd m idl) by assumption. reflexivity. Qed.
Lemma alias_mulw_row2 : forall nm nd nk m idl,
ew E nm = Z_to_bv 64 m -> ew E nd = Z_to_bv 64 idl -> ew E nk = Z_to_bv 64 (2 * ((m - 1) * idl)) -> 1 <= m <= 2048 -> 0 <= idl <= 256 ->
sv_denot E (SAlu ALU_SLL (SMdw M_MUL (SOff nm (-1)) (SOff nd 0)) (SLit 1)) = sv_denot E (SOff nk 0).
Proof.
intros nm nd nk m idl Hm Hd Hk Rm Rd.
assert (Hp : 0 <= (m - 1) * idl <= 2047 * 256) by (split; [apply Z.mul_nonneg_nonneg; lia | apply Z.mul_le_mono_nonneg; lia]).
apply U_inj. rewrite U_SAlu. cbn [zalu_raw]. rewrite U_SLit. change (Z.land (zcanon 1) 63) with 1.
rewrite (U_mulw_row nm nd m idl Hm Hd Rm Rd), (U_atom E nk _ Hk) by lia.
rewrite Z.shiftl_mul_pow2 by lia. change (2 ^ 1) with 2. rewrite zcanon_id by (unfold M64; lia). lia.
Qed.
End t.
End f.
