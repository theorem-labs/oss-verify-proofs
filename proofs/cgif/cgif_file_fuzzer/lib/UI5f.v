(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.LinuxProcessSem.Sys.Fs Require Import Namei.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YM06 YK0s.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP00.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YN3v.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YO0i YO0f YO0x YO0d YO0e YO03
YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import UH00 UH03 UH02 UN3b YI06 UI5b YI09 YI08 YI0r YI0o
UI1w UI21 UI5o UI5l YI6b YL0g
YI16 YI17 YI14 YI18 YI1a UI5c YI00 UI3u UI22 UI2u UI0l YI5a UI23
YI0a YL00 YI05 UI5n.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require YO07.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YM05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Open Scope bv_scope.
Open Scope Z_scope.
Lemma fs_lookup_head_none : forall p d r q, Fs.fs_sorted ((p, d) :: r) = true -> Fs.path_ltb q p = true -> Fs.fs_lookup ((p, d) :: r) q = None.
Proof.
intros p d r q Hs Hlt. apply Fs.fs_lookup_none_of_keys.
assert (Hh : Fs.fs_lt_head q ((p, d) :: r) = true) by exact Hlt.
exact (fs_lt_head_keys ((p, d) :: r) q Hs Hh).
Qed.
Lemma fs_ext : forall f1 f2, Fs.fs_sorted f1 = true -> Fs.fs_sorted f2 = true ->
(forall q, Fs.fs_lookup f1 q = Fs.fs_lookup f2 q) -> f1 = f2.
Proof.
induction f1 as [|[p d] r1 IH]; intros f2 H1 H2 HL.
- destruct f2 as [|[q e] r2]; [reflexivity|]. specialize (HL q). cbn [Fs.fs_lookup] in HL. rewrite Fs.path_eqb_refl in HL. discriminate HL.
- destruct f2 as [|[q e] r2].
{ specialize (HL p). cbn [Fs.fs_lookup] in HL. rewrite Fs.path_eqb_refl in HL. discriminate HL. }
destruct (Fs.path_eqb p q) eqn:Epq.
+ apply Fs.path_eqb_eq in Epq. subst q.
pose proof (HL p) as Hp. cbn [Fs.fs_lookup] in Hp. rewrite Fs.path_eqb_refl in Hp. injection Hp as <-.
f_equal. rewrite Fs.fs_sorted_cons, Bool.andb_true_iff in H1, H2. destruct H1 as [Hh1 Hr1]. destruct H2 as [Hh2 Hr2].
apply (IH r2 Hr1 Hr2). intros k. destruct (Fs.path_eqb k p) eqn:Ek.
* apply Fs.path_eqb_eq in Ek. subst k.
rewrite (Fs.fs_lookup_none_of_keys r1 p (fs_lt_head_keys r1 p Hr1 Hh1)), (Fs.fs_lookup_none_of_keys r2 p (fs_lt_head_keys r2 p Hr2 Hh2)). reflexivity.
* specialize (HL k). cbn [Fs.fs_lookup] in HL. rewrite Ek in HL. exact HL.
+ exfalso. destruct (Fs.path_ltb p q) eqn:Elt.
* pose proof (HL p) as Hp. cbn [Fs.fs_lookup] in Hp. rewrite Fs.path_eqb_refl, Epq in Hp.
rewrite Fs.fs_sorted_cons, Bool.andb_true_iff in H2. destruct H2 as [Hh2 Hr2].
assert (Hn : Fs.fs_lookup r2 p = None).
{ apply Fs.fs_lookup_none_of_keys. apply (fs_lt_head_keys r2 p Hr2).
destruct r2 as [|[q' d'] r']; [reflexivity|]. cbn [Fs.fs_lt_head] in Hh2 |- *. exact (Fs.path_ltb_trans _ _ _ Elt Hh2). }
rewrite Hn in Hp. discriminate Hp.
* pose proof (Fs.path_ltb_total p q Elt Epq) as Egt.
pose proof (HL q) as Hq. cbn [Fs.fs_lookup] in Hq. rewrite Fs.path_eqb_refl in Hq.
rewrite YK0r.path_eqb_sym, Epq in Hq.
rewrite Fs.fs_sorted_cons, Bool.andb_true_iff in H1. destruct H1 as [Hh1 Hr1].
assert (Hn : Fs.fs_lookup r1 q = None).
{ apply Fs.fs_lookup_none_of_keys. apply (fs_lt_head_keys r1 q Hr1).
destruct r1 as [|[q' d'] r']; [reflexivity|]. cbn [Fs.fs_lt_head] in Hh1 |- *. exact (Fs.path_ltb_trans _ _ _ Egt Hh1). }
rewrite Hn in Hq. discriminate Hq.
Qed.
Section h. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Section S.
Variable API : AllocAPI ubs0_msyms.
Let MR : MR_t := aa_MR API.
Let LAWS : MR_laws ubs0_msyms MR := aa_laws API.
Lemma journal_fs_canon : forall STK sp0 FP L A mem md L' A' mem' md' (f : Fs.Fs),
journal ubs0_msyms MR STK sp0 FP L A mem md L' A' mem' md' -> Fs.fs_sorted (m_fs md) = true -> Fs.fs_sorted f = true ->
(forall q, q <> sink_path -> Fs.fs_lookup f q = Fs.fs_lookup (m_fs md) q) ->
Fs.fs_lookup (m_fs md') sink_path = Fs.fs_lookup f sink_path ->
m_fs md' = f.
Proof using API.
intros STK sp0 FP L A mem md L' A' mem' md' f HJ Hs Hf Hq Hk.
pose proof HJ as (_ & Hos & _). apply fs_ext; [exact (os_step_sorted _ _ _ Hos Hs) | exact Hf |].
intros q. destruct (list_eq_dec (@bv_eq_dec 8) q sink_path) as [-> | Hne]; [exact Hk|].
rewrite (Hq q Hne). exact (os_step_fs _ _ _ Hos q Hne).
Qed.
Lemma journal_fs_set : forall STK sp0 FP L A mem md L' A' mem' md' d,
journal ubs0_msyms MR STK sp0 FP L A mem md L' A' mem' md' -> Fs.fs_sorted (m_fs md) = true ->
Fs.fs_lookup (m_fs md') sink_path = Some d -> m_fs md' = Fs.fs_set (m_fs md) sink_path d.
Proof using API.
intros STK sp0 FP L A mem md L' A' mem' md' d HJ Hs Hk.
apply (journal_fs_canon STK sp0 FP L A mem md L' A' mem' md' _ HJ Hs (Fs.fs_set_sorted _ _ _ Hs)).
- intros q Hq. apply YK0r.fs_lookup_set_other. exact Hq.
- rewrite YK0r.fs_lookup_set_same. exact Hk.
Qed.
Lemma journal_fs_same : forall STK sp0 FP L A mem md L' A' mem' md',
journal ubs0_msyms MR STK sp0 FP L A mem md L' A' mem' md' -> Fs.fs_sorted (m_fs md) = true ->
Fs.fs_lookup (m_fs md') sink_path = Fs.fs_lookup (m_fs md) sink_path -> m_fs md' = m_fs md.
Proof using API.
intros STK sp0 FP L A mem md L' A' mem' md' HJ Hs Hk.
apply (journal_fs_canon STK sp0 FP L A mem md L' A' mem' md' _ HJ Hs Hs); [intros q _; reflexivity | exact Hk].
Qed.
Lemma journal_sorted : forall STK sp0 FP L A mem md L' A' mem' md',
journal ubs0_msyms MR STK sp0 FP L A mem md L' A' mem' md' -> Fs.fs_sorted (m_fs md) = true -> Fs.fs_sorted (m_fs md') = true.
Proof using API. intros STK sp0 FP L A mem md L' A' mem' md' (_ & Hos & _) Hs. exact (os_step_sorted _ _ _ Hos Hs). Qed.
Lemma journal_fds_restored : forall STK sp0 FP L A mem md L' A' mem' md',
journal ubs0_msyms MR STK sp0 FP L A mem md L' A' mem' md' -> sink_none ubs0_msyms mem md -> sink_none ubs0_msyms mem' md' ->
forall k, fd_lookup (m_fds md') k = fd_lookup (m_fds md) k.
Proof using API. intros STK sp0 FP L A mem md L' A' mem' md' (_ & Hos & _) H0 H1. exact (sink_fds_restored ubs0_msyms FP mem md mem' md' Hos H0 H1). Qed.
End S.
Lemma zbytes_length : forall pl, length (zbytes pl) = length pl.
Proof using. intros pl. unfold zbytes. apply length_map. Qed.
Lemma blk_data_garr8 : forall m p (pl : list byte), blk_data ubs0_msyms m p pl -> garr8 ubs0segs m p (zbytes pl).
Proof using.
intros m p pl H j Hj. rewrite zbytes_length in Hj.
assert (Hb : mbyte ubs0segs m (p + Z.of_nat j) = nth_error pl j).
{ etransitivity; [exact (H (Z.of_nat j) ltac:(lia))|]. rewrite Nat2Z.id. reflexivity. }
destruct (nth_error pl j) as [b|] eqn:En; [| apply nth_error_None in En; lia].
assert (Hn : nth j (zbytes pl) 0 = bv_unsigned b).
{ apply nth_error_nth. unfold zbytes. rewrite nth_error_map, En. reflexivity. }
pose proof (bv_unsigned_in_range 8 b) as Rb. change (bv_modulus 8) with 256 in Rb.
rewrite Hn. split; [|lia]. intros k Hk. destruct k; [|cbn in Hk; lia]. cbn [Z.of_nat]. rewrite Z.add_0_r, Hb. f_equal.
unfold le_byte. change (8 * Z.of_nat 1) with 8. change (8 * 0) with 0. rewrite Z.shiftr_0_r. change (2 ^ 8) with 256.
rewrite !Z.mod_small by lia. symmetry. apply Z_to_bv_bv_unsigned.
Qed.
Definition ff_tree (K : lleaf -> TSet) (fs : Fs.Fs) (P : list Z) : TSet :=
match ff_cfg P with
| None => ff_leaf K fs
| Some (g, loops, rest) =>
if g_opens g
then openat_shape fs (ff_unl K fs) (ff_unl K (Fs.fs_set fs sink_path (bytes (ff_content g loops rest))))
else ff_unl K fs
end.
Lemma ff_libk_tree : forall pl fs K, ff_libk pl fs K = ff_tree K fs (zbytes pl).
Proof using. intros. reflexivity. Qed.
Lemma hdr5_short : forall P, Z.of_nat (length P) < 14 -> fst (fst (hdr5 P)) = true.
Proof using.
intros P HP. unfold hdr5.
assert (R0 : forall n, 0 < n -> YO07.rd [] n = (true, [], [])) by (intros n Hn; apply rd_short; cbn; lia).
destruct (Z_lt_le_dec (Z.of_nat (length P)) 2) as [H1|H1].
{ rewrite (rd_short P 2 H1), !R0 by lia. reflexivity. }
rewrite (rd_ok P 2) by lia.
destruct (Z_lt_le_dec (Z.of_nat (length (skipn (Z.to_nat 2) P))) 2) as [H2|H2].
{ rewrite (rd_short _ 2 H2), !R0 by lia. reflexivity. }
rewrite (rd_ok (skipn (Z.to_nat 2) P) 2) by lia.
destruct (Z_lt_le_dec (Z.of_nat (length (skipn (Z.to_nat 2) (skipn (Z.to_nat 2) P)))) 4) as [H3|H3].
{ rewrite (rd_short _ 4 H3), !R0 by lia. reflexivity. }
rewrite (rd_ok (skipn (Z.to_nat 2) (skipn (Z.to_nat 2) P)) 4) by lia.
destruct (Z_lt_le_dec (Z.of_nat (length (skipn (Z.to_nat 4) (skipn (Z.to_nat 2) (skipn (Z.to_nat 2) P))))) 4) as [H4|H4].
{ rewrite (rd_short _ 4 H4), !R0 by lia. reflexivity. }
rewrite (rd_ok (skipn (Z.to_nat 4) (skipn (Z.to_nat 2) (skipn (Z.to_nat 2) P))) 4) by lia.
destruct (Z_lt_le_dec (Z.of_nat (length (skipn (Z.to_nat 4) (skipn (Z.to_nat 4) (skipn (Z.to_nat 2) (skipn (Z.to_nat 2) P)))))) 2) as [H5|H5].
{ rewrite (rd_short _ 2 H5). reflexivity. }
exfalso. rewrite !length_skipn in H5. change (Z.to_nat 4) with 4%nat in H5. change (Z.to_nat 2) with 2%nat in H5. lia.
Qed.
Lemma ff_cfg_hdr_short : forall P, fst (fst (hdr5 P)) = true -> ff_cfg P = None.
Proof using.
intros P HP. unfold ff_cfg. destruct (hdr5 P) as [[e [[[[W H] attr] gen] ngp]] s5]. cbn [fst] in HP. subst e.
destruct (if YO07.flag attr 4 then (false, [], s5) else YO07.rd s5 (ngp * 3)) as [[e6 gp] s6]. reflexivity.
Qed.
Lemma ff_cfg_pal_short : forall P W H attr gen ngp,
hdr5 P = (false, (W, H, attr, gen, ngp), skipn 14 P) -> Z.land attr 4 = 0 ->
14 <= Z.of_nat (length P) -> Z.of_nat (length P) < 14 + 3 * ngp -> ff_cfg P = None.
Proof using.
intros P W H attr gen ngp Hh Ha Hl Hs. unfold ff_cfg. rewrite Hh. unfold YO07.flag. rewrite (proj2 (Z.eqb_eq _ _) Ha). cbn [negb].
rewrite rd_short by (rewrite length_skipn; lia). reflexivity.
Qed.
Lemma ff_cfg_too_large : forall P W H attr gen ngp,
hdr5 P = (false, (W, H, attr, gen, ngp), skipn 14 P) -> 100000000 < W * H -> ff_cfg P = None.
Proof using.
intros P W H attr gen ngp Hh HWH. unfold ff_cfg. rewrite Hh.
destruct (if YO07.flag attr 4 then (false, [], skipn 14 P) else YO07.rd (skipn 14 P) (ngp * 3)) as [[e6 gp] s6].
destruct e6; [reflexivity|]. cbn [orb]. destruct (Z.ltb_spec 100000000 (W * H)); [reflexivity | lia].
Qed.
Definition loop_file (G : YO07.gcfg) (k : nat) (gs : YO07.gif_st) (s : list Z) : list Z :=
concat (YO07.close_gif G (YO07.frames_loop k G gs s)) ++ [59].
Lemma ff_file_loop : forall G loops rest, ff_file G loops rest = loop_file G 16 (gs0 G loops) rest.
Proof using. intros. reflexivity. Qed.
Lemma loop_file_step : forall G k gs s attr gen delay tidx nlp lpal img s7,
parse_frame G s = (true, (attr, gen, delay, tidx, nlp, lpal, img), s7) ->
loop_file G (Datatypes.S k) gs s = loop_file G k (YO07.add_frame G gs attr gen delay tidx nlp lpal img) s7.
Proof using. intros G k gs s attr gen delay tidx nlp lpal img s7 HP. unfold loop_file. rewrite frames_loop_step, HP. reflexivity. Qed.
Lemma loop_file_stop : forall G k gs s, fst (fst (parse_frame G s)) = false -> loop_file G k gs s = loop_file G 0 gs s.
Proof using.
intros G [|k] gs s HP; [reflexivity|]. unfold loop_file. rewrite frames_loop_step.
destruct (parse_frame G s) as [[ok fl] s7]. destruct fl as [[[[[[a ge] d] t] n] lp] im]. cbn [fst] in HP. subst ok. reflexivity.
Qed.
Section S2.
Variable API : AllocAPI ubs0_msyms.
Let MR : MR_t := aa_MR API.
Definition leaf_post (regs0 : bvmap 5 word) (L : layout) (A : astate) (mem : word -> option byte) (md : Model) (bfin : rbound)
(fs' : Fs.Fs) (c' : config) : Prop :=
exists L' A' regs' mem' md',
c' = mkCfg (mkst regs' (getr regs0 1) mem' (seg_rom ubs0segs)) md' /\
journal ubs0_msyms MR LIB_STACK (spZ regs0) [sink_token] L A mem md L' A' mem' md' /\
regs_preserved regs0 regs' /\
st_init_done A' = true /\
getr regs' 10 = Z_to_bv 64 0 /\
sink_none ubs0_msyms mem' md' /\
(forall blk, In blk (blocks L A) -> In blk (blocks L' A')) /\
m_fs md' = fs' /\
res_ok A' bfin.
End S2.
Section S3.
Variable API : AllocAPI ubs0_msyms.
Let MR : MR_t := aa_MR API.
Let LAWS : MR_laws ubs0_msyms MR := aa_laws API.
Hypothesis IMG : img_laws ubs0_msyms MR.
Lemma jfree_at_res :
forall E ss ms STK sp0 FP L A mem md Lc Ac mdc a n spc raw b,
st_ok ubs0segs E ss ms -> ss_pc ss = ubs0_A_free -> ss_resv ss = None ->
journal ubs0_msyms MR STK sp0 FP L A mem md Lc Ac (ms_mem ms) mdc ->
In (a, n) (blocks Lc Ac) -> res_ok Ac b ->
getr (ms_regs ms) 10 = Z_to_bv 64 a ->
getr (ms_regs ms) 2 = Z_to_bv 64 spc -> 0 <= spc < 2 ^ 64 -> spc mod 16 = 0 ->
sp0 - STK <= spc - ALLOC_STACK -> spc <= sp0 ->
getr (ms_regs ms) 4 = Z_to_bv 64 (ms_tp ubs0_msyms) ->
getr (ms_regs ms) 1 = raw -> YK0s.ret_ok raw ->
(In (a, n) (blocks L A) -> forall i, 0 <= i < n -> inFP FP (a + i)) ->
SR ubs0segs (mkCfg ms mdc)
(fun c' => exists L2 A2 regs2 mem2 md2,
c' = mkCfg (mkst regs2 raw mem2 (seg_rom ubs0segs)) md2 /\
journal ubs0_msyms MR STK sp0 FP L A mem md L2 A2 mem2 md2 /\
regs_preserved (ms_regs ms) regs2 /\
rm1 (a, n) (blocks Lc Ac) (blocks L2 A2) /\
(forall b' m i, In (b', m) (blocks L2 A2) -> 0 <= i < m -> mbyte ubs0segs mem2 (b' + i) = mbyte ubs0segs (ms_mem ms) (b' + i)) /\
(forall x, alloc_ceiling <= x < 2 ^ 64 -> ~ (spc - ALLOC_STACK <= x < spc) ->
mbyte ubs0segs mem2 x = mbyte ubs0segs (ms_mem ms) x /\ (writable_at ubs0segs (ms_mem ms) x <-> writable_at ubs0segs mem2 x)) /\
st_init_done A2 = true /\ res_ok A2 (rb_free b n)).
Proof using IMG LAWS.
intros E ss ms STK sp0 FP L A mem md Lc Ac mdc a n spc raw b HS Hpc Hrv HJ Hin HRb Ha0 Hsp Hspc Hal Hlo Hhi Htp Hra Hraw HFP.
assert (Hsp' : spZ (ms_regs ms) = spc) by (unfold spZ; rewrite Hsp; apply unsigned_lit_small; exact Hspc).
rewrite (st_ok_mkst ubs0segs E ss ms HS Hrv), Hpc.
apply blocks_In in Hin as (p & Hp & Hpin).
eapply SR_mono.
{ eapply (cg_free_res ubs0_msyms MR LAWS ubs0_errno_low IMG (aa_free API) STK sp0 FP L A mem md Lc Ac (ms_regs ms) (ms_mem ms) mdc p n b HJ Hpin HRb).
- rewrite Hp. exact Ha0.
- rewrite Hra. exact Hraw.
- rewrite Hsp'. exact Hal.
- rewrite Hsp'. exact Hlo.
- rewrite Hsp'. exact Hhi.
- exact Htp.
- rewrite Hp. exact HFP. }
intros c' (L2 & A2 & regs2 & mem2 & md2 & -> & HJ2 & HP2 & Hrm & Hkeep & Hhi2 & Hid2 & HR2).
exists L2, A2, regs2, mem2, md2. rewrite Hra. split; [reflexivity|]. split; [exact HJ2|]. split; [exact HP2|].
rewrite Hp in Hrm. split; [exact Hrm|]. split; [exact Hkeep|]. split; [| split; [exact Hid2 | exact HR2]].
intros x Hx Hnx. apply Hhi2; [exact Hx|]. rewrite Hsp'. exact Hnx.
Qed.
Lemma jfree_tmp_sink_res :
forall E ss ms STK sp0 FP L A mem md Lc Ac mdc a n spc raw f S b,
st_ok ubs0segs E ss ms -> ss_pc ss = ubs0_A_free -> ss_resv ss = None ->
journal ubs0_msyms MR STK sp0 FP L A mem md Lc Ac (ms_mem ms) mdc -> st_init_done Ac = true ->
In (a, n) (blocks Lc Ac) -> (In (a, n) (blocks L A) -> forall i, 0 <= i < n -> False) ->
In (f, FILE_BLOCK) (blocks Lc Ac) -> (a + n <= f \/ f + FILE_BLOCK <= a) ->
sink_at ubs0_msyms (ms_mem ms) mdc f S -> res_ok Ac b ->
getr (ms_regs ms) 10 = Z_to_bv 64 a ->
getr (ms_regs ms) 2 = Z_to_bv 64 spc -> 0 <= spc < 2 ^ 64 -> spc mod 16 = 0 ->
sp0 - STK <= spc - ALLOC_STACK -> spc <= sp0 ->
getr (ms_regs ms) 4 = Z_to_bv 64 (ms_tp ubs0_msyms) ->
getr (ms_regs ms) 1 = raw -> YK0s.ret_ok raw ->
SR ubs0segs (mkCfg ms mdc)
(fun c' => exists L2 A2 regs2 mem2 md2,
c' = mkCfg (mkst regs2 raw mem2 (seg_rom ubs0segs)) md2 /\
journal ubs0_msyms MR STK sp0 FP L A mem md L2 A2 mem2 md2 /\
st_init_done A2 = true /\
regs_preserved (ms_regs ms) regs2 /\
rm1 (a, n) (blocks Lc Ac) (blocks L2 A2) /\
(forall b' m i, In (b', m) (blocks L2 A2) -> 0 <= i < m -> mbyte ubs0segs mem2 (b' + i) = mbyte ubs0segs (ms_mem ms) (b' + i)) /\
(forall x, alloc_ceiling <= x < 2 ^ 64 -> ~ (spc - ALLOC_STACK <= x < spc) ->
mbyte ubs0segs mem2 x = mbyte ubs0segs (ms_mem ms) x /\ (writable_at ubs0segs (ms_mem ms) x <-> writable_at ubs0segs mem2 x)) /\
(sink_at ubs0_msyms mem2 md2 f S /\ In (f, FILE_BLOCK) (blocks L2 A2)) /\
res_ok A2 (rb_free b n)).
Proof using IMG LAWS.
intros E ss ms STK sp0 FP L A mem md Lc Ac mdc a n spc raw f S b HS Hpc Hrv HJ Hid Hin Hnew Hfin Hsep HSK HRb H10 H2 Hspc Hal Hlo Hhi H4 H1 Hraw.
pose proof (proj1 alloc_ceiling_val) as Hac.
pose proof (journal_restart ubs0_msyms MR _ _ _ _ _ _ _ _ _ _ _ [(a, a + n)] HJ) as HJl.
destruct (blocks_range _ _ LAWS Lc Ac (ms_mem ms) mdc a n (proj1 HJ) Hin) as [Ha0 Ha1].
eapply SR_mono.
{ eapply (jfree_at_res E ss ms STK sp0 [(a, a + n)] Lc Ac (ms_mem ms) mdc Lc Ac mdc a n spc raw b);
[ exact HS | exact Hpc | exact Hrv | exact HJl | exact Hin | exact HRb | exact H10 | exact H2 | exact Hspc | exact Hal | exact Hlo | exact Hhi | exact H4 | exact H1 | exact Hraw | ].
intros _ i Hi. exists (a, a + n). split; [left; reflexivity | cbn [fst snd]; lia]. }
cbv beta. intros c' (L2 & A2 & regs2 & mem2 & md2 & -> & HJ2 & HP2 & Hrm & Hkeep & Hhi2 & Hid2 & HR2).
assert (HK : sink_at ubs0_msyms mem2 md2 f S /\ In (f, FILE_BLOCK) (blocks L2 A2)).
{ eapply (sink_kept ubs0_msyms MR); [exact HJ2 | | exact Hfin | | exact HSK].
- intros (r & [<- | []] & Hr). cbn [fst snd] in Hr. lia.
- intros x Hx (r & [<- | []] & Hr). cbn [fst snd] in Hr. lia. }
exists L2, A2, regs2, mem2, md2. split; [reflexivity|]. split.
{ eapply (journal_sub_gen ubs0_msyms MR LAWS); [exact HJ | exact HJ2 | lia | lia |].
intros x (r & [<- | []] & Hr). cbn [fst snd] in Hr. right. exists a, n. split; [exact Hin|]. split; [|lia].
intros H0. exact (Hnew H0 (x - a) ltac:(lia)). }
split; [exact Hid2|]. split; [exact HP2|]. split; [exact Hrm|]. split; [exact Hkeep|]. split; [exact Hhi2|]. split; [exact HK | exact HR2].
Qed.
Lemma jfree_tmp_tok_res :
forall E ss ms STK sp0 FP L A mem md Lc Ac mdc a n spc raw b,
st_ok ubs0segs E ss ms -> ss_pc ss = ubs0_A_free -> ss_resv ss = None ->
journal ubs0_msyms MR STK sp0 FP L A mem md Lc Ac (ms_mem ms) mdc -> st_init_done Ac = true ->
In (a, n) (blocks Lc Ac) -> (In (a, n) (blocks L A) -> forall i, 0 <= i < n -> False) -> res_ok Ac b ->
getr (ms_regs ms) 10 = Z_to_bv 64 a ->
getr (ms_regs ms) 2 = Z_to_bv 64 spc -> 0 <= spc < 2 ^ 64 -> spc mod 16 = 0 ->
sp0 - STK <= spc - ALLOC_STACK -> spc <= sp0 ->
getr (ms_regs ms) 4 = Z_to_bv 64 (ms_tp ubs0_msyms) ->
getr (ms_regs ms) 1 = raw -> YK0s.ret_ok raw ->
SR ubs0segs (mkCfg ms mdc)
(fun c' => exists L2 A2 regs2 mem2 md2,
c' = mkCfg (mkst regs2 raw mem2 (seg_rom ubs0segs)) md2 /\
journal ubs0_msyms MR STK sp0 FP L A mem md L2 A2 mem2 md2 /\
journal ubs0_msyms MR STK sp0 [(a, a + n)] Lc Ac (ms_mem ms) mdc L2 A2 mem2 md2 /\
st_init_done A2 = true /\
regs_preserved (ms_regs ms) regs2 /\
rm1 (a, n) (blocks Lc Ac) (blocks L2 A2) /\
(forall b' m i, In (b', m) (blocks L2 A2) -> 0 <= i < m -> mbyte ubs0segs mem2 (b' + i) = mbyte ubs0segs (ms_mem ms) (b' + i)) /\
(forall x, alloc_ceiling <= x < 2 ^ 64 -> ~ (spc - ALLOC_STACK <= x < spc) ->
mbyte ubs0segs mem2 x = mbyte ubs0segs (ms_mem ms) x /\ (writable_at ubs0segs (ms_mem ms) x <-> writable_at ubs0segs mem2 x)) /\
res_ok A2 (rb_free b n)).
Proof using IMG LAWS.
intros E ss ms STK sp0 FP L A mem md Lc Ac mdc a n spc raw b HS Hpc Hrv HJ Hid Hin Hnew HRb H10 H2 Hspc Hal Hlo Hhi H4 H1 Hraw.
pose proof (proj1 alloc_ceiling_val) as Hac.
pose proof (journal_restart ubs0_msyms MR _ _ _ _ _ _ _ _ _ _ _ [(a, a + n)] HJ) as HJl.
destruct (blocks_range _ _ LAWS Lc Ac (ms_mem ms) mdc a n (proj1 HJ) Hin) as [Ha0 Ha1].
eapply SR_mono.
{ eapply (jfree_at_res E ss ms STK sp0 [(a, a + n)] Lc Ac (ms_mem ms) mdc Lc Ac mdc a n spc raw b);
[ exact HS | exact Hpc | exact Hrv | exact HJl | exact Hin | exact HRb | exact H10 | exact H2 | exact Hspc | exact Hal | exact Hlo | exact Hhi | exact H4 | exact H1 | exact Hraw | ].
intros _ i Hi. exists (a, a + n). split; [left; reflexivity | cbn [fst snd]; lia]. }
cbv beta. intros c' (L2 & A2 & regs2 & mem2 & md2 & -> & HJ2 & HP2 & Hrm & Hkeep & Hhi2 & Hid2 & HR2).
exists L2, A2, regs2, mem2, md2. split; [reflexivity|]. split.
{ eapply (journal_sub_gen ubs0_msyms MR LAWS); [exact HJ | exact HJ2 | lia | lia |].
intros x (r & [<- | []] & Hr). cbn [fst snd] in Hr. right. exists a, n. split; [exact Hin|]. split; [|lia].
intros H0. exact (Hnew H0 (x - a) ltac:(lia)). }
split; [exact HJ2|]. split; [exact Hid2|]. split; [exact HP2|]. split; [exact Hrm|]. split; [exact Hkeep|]. split; [exact Hhi2 | exact HR2].
Qed.
Lemma jmalloc_at_res :
forall E ss ms STK sp0 FP L A mem md Lc Ac mdc n spc raw b,
st_ok ubs0segs E ss ms -> ss_pc ss = ubs0_A_malloc -> ss_resv ss = None ->
journal ubs0_msyms MR STK sp0 FP L A mem md Lc Ac (ms_mem ms) mdc ->
st_init_done Ac = true ->
getr (ms_regs ms) 10 = Z_to_bv 64 n -> res_ok Ac b -> room b n ->
getr (ms_regs ms) 2 = Z_to_bv 64 spc -> 0 <= spc < 2 ^ 64 -> spc mod 16 = 0 ->
sp0 - STK <= spc - ALLOC_STACK -> spc <= sp0 ->
getr (ms_regs ms) 4 = Z_to_bv 64 (ms_tp ubs0_msyms) ->
getr (ms_regs ms) 1 = raw -> YK0s.ret_ok raw ->
SR ubs0segs (mkCfg ms mdc)
(fun c' => exists L2 A2 regs2 mem2 md2 (res : Z),
c' = mkCfg (mkst regs2 raw mem2 (seg_rom ubs0segs)) md2 /\
journal ubs0_msyms MR STK sp0 FP L A mem md L2 A2 mem2 md2 /\
st_init_done A2 = true /\
regs_preserved (ms_regs ms) regs2 /\
getr regs2 10 = Z_to_bv 64 res /\
(res <> 0 /\ res mod 16 = 0 /\
(exists b1 b2, blocks L2 A2 = b1 ++ (res, n) :: b2 /\ blocks Lc Ac = b1 ++ b2) /\
(forall blc i, In (res, n) blc -> 0 <= i < n -> wr_byte STK sp0 FP (blocks L A) blc (res + i))) /\
(forall b' m i, In (b', m) (blocks Lc Ac) -> 0 <= i < m -> mbyte ubs0segs mem2 (b' + i) = mbyte ubs0segs (ms_mem ms) (b' + i)) /\
(forall x, alloc_ceiling <= x < 2 ^ 64 -> ~ (spc - ALLOC_STACK <= x < spc) ->
mbyte ubs0segs mem2 x = mbyte ubs0segs (ms_mem ms) x /\ (writable_at ubs0segs (ms_mem ms) x <-> writable_at ubs0segs mem2 x)) /\
res_ok A2 (rb_malloc b n)).
Proof using IMG LAWS.
intros E ss ms STK sp0 FP L A mem md Lc Ac mdc n spc raw b HS Hpc Hrv HJ Hid Ha0 HRb HRm Hsp Hspc Hal Hlo Hhi Htp Hra Hraw.
assert (Hsp' : spZ (ms_regs ms) = spc) by (unfold spZ; rewrite Hsp; apply unsigned_lit_small; exact Hspc).
rewrite (st_ok_mkst ubs0segs E ss ms HS Hrv), Hpc.
eapply SR_mono.
{ eapply (cg_malloc_res ubs0_msyms MR LAWS ubs0_errno_low IMG (aa_malloc API) STK sp0 FP L A mem md Lc Ac (ms_regs ms) (ms_mem ms) mdc n b HJ Hid Ha0 HRb HRm).
- rewrite Hra. exact Hraw.
- rewrite Hsp'. exact Hal.
- rewrite Hsp'. exact Hlo.
- rewrite Hsp'. exact Hhi.
- exact Htp. }
intros c' (L2 & A2 & regs2 & mem2 & md2 & res & -> & HJ2 & Hid2 & HP2 & Hr10 & Hres & Hkeep & Hhi2 & HR2).
exists L2, A2, regs2, mem2, md2, res. rewrite Hra. split; [reflexivity|]. split; [exact HJ2|]. split; [exact Hid2|].
split; [exact HP2|]. split; [exact Hr10|]. split; [exact Hres|]. split; [exact Hkeep|]. split; [|exact HR2].
intros x Hx Hnx. apply Hhi2; [exact Hx|]. rewrite Hsp'. exact Hnx.
Qed.
End S3.
End h.
Lemma SR_here {fx : YK11.FPState} {rc : YM05.RunCeil} : forall segs (c : config) (Q : config -> Prop), Q c -> SR segs c Q.
Proof. intros segs c Q HQ T HT. exact (HT c HQ). Qed.
