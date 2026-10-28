(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Sem.
From OssFuzzTheorems.cgif.cgif_file_fuzzer.images Require Import Asan.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YO0d.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YK11 YK00 YK0h YK14 YK1b YK15 YK18 YK0p YP0n YK0s YM02 YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP08 YP03 YP0g YN3q YN3v YI04 YL0a YL0b YL09 YK04 YA0i YA0n YA0o YA0p YA0m YK09 YA0e YG00 YG01 YG0f YG0v YG0n YG0d YCe5.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib.A Require Import AB1v AB12 AF0l AB1h AB13 AF0m AD2j AD2i AD1t AD1y AD20 AD1v AD26 AD24 AD21.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YM05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Open Scope Z_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Lemma rs_not_owned_static : forallb (fun h : Z * Z => (fst h + snd h <=? RS_LO) || (RS_HI <=? fst h))%bool Tfib_owned_static = true.
Proof. vm_compute. reflexivity. Qed.
Lemma st_ok_app_regions {fx : YK11.FPState} : forall E ss ms rs',
st_ok tfibsegs E ss ms -> regions_wf rs' = true -> Forall (region_ok tfibsegs E (ms_mem ms)) rs' -> pairwise_disjoint E rs' ->
(forall r1 r2, In r1 (ss_mem ss) -> In r2 rs' -> extent_disjoint E r1 r2) ->
st_ok tfibsegs E (mkSS (ss_pc ss) (ss_regs ss) (ss_mem ss ++ rs') (ss_resv ss) (ss_facts ss)) ms.
Proof.
intros E ss ms rs' (H1 & H2 & H3 & H4 & H5 & H6 & H7 & (Hwf & Hok & Hpd) & H9) Hwf' Hok' Hpd' Hx.
unfold st_ok; cbn. repeat (split; [assumption|]). split; [|exact H9]. split; [| split].
- clear -Hwf Hwf'. induction (ss_mem ss) as [|r rs IH]; cbn in *; [exact Hwf'|]. apply andb_prop in Hwf as [Ha Hb]. rewrite Ha, (IH Hb). reflexivity.
- apply Forall_app. split; assumption.
- apply YP08.pairwise_disjoint_app; assumption.
Qed.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YO09.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib.A Require Import AE2k AD1u.
Section e. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {LS : lib_shape}.
Section Rd.
Variable B : asyms.
Hypothesis HB : TfibSyms B.
Hypothesis ARL : AR_laws tfibsegs B.
Lemma wvb_fs' : forall l mat (m : Model), m_fs (with_vm_backing l mat m) = m_fs m.
Proof. intros l mat m. destruct m; reflexivity. Qed.
Lemma wvb_fds' : forall l mat (m : Model), m_fds (with_vm_backing l mat m) = m_fds m.
Proof. intros l mat m. destruct m; reflexivity. Qed.
Lemma frame_of_skel' : forall E rs rs' (m m' : word -> option byte), skeleton rs = skeleton rs' -> frame_of E rs' m m' -> frame_of E rs m m'.
Proof. intros E rs rs' m m' Hsk HF. eapply frame_of_trans; [exact Hsk | apply frame_of_refl | exact HF]. Qed.
Lemma apresent_some' : forall (H : word -> bool) mem a, apresent H mem a -> mem (Z_to_bv 64 a) <> None.
Proof. intros H mem a [_ [bb Hb]]. rewrite Hb. discriminate. Qed.
Lemma mem_grows_of_apresent : forall (H : word -> bool) (m m' : word -> option byte),
(forall a, apresent H m a -> apresent H m' a) -> mem_grows (mrestrict H m) (mrestrict H m').
Proof.
intros H m m' Hp x Hx. pose proof (u64_range x) as R.
assert (A : apresent H m (bv_unsigned x)).
{ unfold apresent, mrestrict in *. rewrite Z_to_bv_bv_unsigned. destruct (H x); [exfalso; exact (Hx eq_refl)|].
split; [reflexivity|]. destruct (m x) as [b|]; [exists b; reflexivity | exfalso; exact (Hx eq_refl)]. }
destruct (Hp _ A) as [Hh [b Hb]]. rewrite Z_to_bv_bv_unsigned in Hh, Hb. unfold mrestrict. rewrite Hh, Hb. discriminate.
Qed.
Lemma seg_win_visible : forall (W : world tfibsegs) a n x,
seg_win_check tfibsegs a (Z.to_nat n) = true -> 0 <= n -> 0 <= a -> a + n <= 2 ^ 64 -> a <= x < a + n -> w_H W (Z_to_bv 64 x) = false.
Proof.
intros W a n x Hck Hn Ha Han Hx.
pose proof (seg_win_wview tfibsegs a n (fun _ => None) x Hck Hn Hx) as Hw.
destruct (w_H W (Z_to_bv 64 x)) eqn:Eh; [|reflexivity]. exfalso.
pose proof (w_Hoff W (Z_to_bv 64 x) Eh) as Hseg. unfold wview in Hw. rewrite Hseg in Hw. exact (Hw eq_refl).
Qed.
Lemma rs_in_img : forall x, RS_LO <= x < RS_HI -> in_img tfibsegs x.
Proof. intros x Hx. unfold RS_LO, RS_HI in Hx. apply in_img_rw. lia. Qed.
Lemma rs_not_owned : forall ly S W mem md x, AR tfibsegs B ly S W mem md -> RS_LO <= x < RS_HI -> ~ aowned B ly S x.
Proof.
intros ly S W mem md x HAR Hx Ho.
apply (proj1 (al_owned_image _ _ ARL ly S W mem md x HAR (rs_in_img x Hx))) in Ho.
rewrite (ts_owned B HB) in Ho. apply Exists_exists in Ho as (h & Hin & Hz).
pose proof (proj1 (forallb_forall _ _) rs_not_owned_static h Hin) as Hc. cbn beta in Hc.
unfold in_zr in Hz. apply orb_prop in Hc as [Hc|Hc]; apply Z.leb_le in Hc; lia.
Qed.
Lemma AR_after_win_write : forall ly S W mem md md' (a : Z) bs,
AR tfibsegs B ly S W mem md -> RS_LO <= a -> a + Z.of_nat (length bs) <= RS_HI ->
m_vmmaps md' = m_vmmaps md -> m_vm_lazy md' = m_vm_lazy md -> eager_used md' = eager_used md ->
AR tfibsegs B ly S W (wbytes mem (Z_to_bv 64 a) bs) md'.
Proof.
intros ly S W mem md md' a bs HAR Hlo Hhi Hv Hl He.
assert (Hau : bv_unsigned (Z_to_bv 64 a) = a) by (unfold RS_LO, RS_HI in *; apply u64_lit; lia).
apply (al_frame _ _ ARL ly S W mem md _ md' HAR); [| | exact Hv | exact Hl | exact He |].
3:{
intros x Hx _. unfold in_band_rw, kLowShadowBeg, kLowShadowEnd, kHighShadowBeg, kHighShadowEnd, RS_LO, RS_HI in *.
apply wbytes_above; unfold w64; rewrite Hau, u64_lit by lia; lia. }
- intros x Hx Ho. unfold aview, mbyte, mrestrict.
assert (Hout : x < a \/ a + Z.of_nat (length bs) <= x).
{ destruct (Z.lt_ge_cases x a); [left; lia|]. destruct (Z.le_gt_cases (a + Z.of_nat (length bs)) x); [right; lia|].
exfalso. exact (rs_not_owned ly S W mem md x HAR ltac:(lia) Ho). }
destruct (w_H W (Z_to_bv 64 x)); [reflexivity|]. unfold RS_LO, RS_HI in *.
destruct Hout as [Hout|Hout].
+ rewrite wbytes_below; [reflexivity | rewrite Hau; lia | rewrite Hau, u64_lit by lia; lia].
+ rewrite wbytes_above; [reflexivity | rewrite Hau, u64_lit by lia; lia].
- intros x Hv0. unfold aview, mbyte, mrestrict in *. destruct (w_H W (Z_to_bv 64 x)); [exact Hv0|].
destruct (mem (Z_to_bv 64 x)) as [b0|] eqn:Em.
+ pose proof (wbytes_grows bs mem (Z_to_bv 64 a) (Z_to_bv 64 x) ltac:(rewrite Em; discriminate)) as G.
destruct (wbytes mem (Z_to_bv 64 a) bs (Z_to_bv 64 x)); [cbn; discriminate | exfalso; exact (G eq_refl)].
+ destruct (wbytes mem (Z_to_bv 64 a) bs (Z_to_bv 64 x)); [cbn; discriminate | exact Hv0].
Qed.
Lemma srr_read_win : forall E ss ms (W : world tfibsegs) md fd pth (off : word) data bs (a cnt : Z),
st_ok_ecall tfibsegs E ss (restrict (w_H W) ms) -> ss_resv ss = None ->
bv_unsigned (sv_denot E (sr_get (ss_regs ss) 17%bv)) = 63 ->
sv_denot E (sr_get (ss_regs ss) 10%bv) = fd -> fd32 fd = fd ->
fd_lookup (m_fds md) fd = Some (FdFile pth off) -> fs_lookup (m_fs md) pth = Some data ->
bv_unsigned (sv_denot E (sr_get (ss_regs ss) 11%bv)) = a ->
bv_unsigned (sv_denot E (sr_get (ss_regs ss) 12%bv)) = cnt -> 0 < cnt <= 65536 ->
file_read data off (sv_denot E (sr_get (ss_regs ss) 12%bv)) = bs ->
win_check (ss_mem ss) a 65536 = true -> seg_win_check tfibsegs a (Z.to_nat 65536) = true -> 0 <= a -> a + 65536 <= 2 ^ 47 ->
SRr tfibsegs W (mkCfg ms md)
(fun W' c' => W' = W /\ exists regs md',
ms = pend_at regs (Z_to_bv 64 (ss_pc ss)) (ms_mem ms) (seg_rom tfibsegs) /\
c' = mkCfg (mkst (regupd regs 10%bv (len_word bs)) (v_addi (Z_to_bv 64 (ss_pc ss)) 4)
(wbytes (ms_mem ms) (Z_to_bv 64 a) bs) (seg_rom tfibsegs)) md' /\
regs_ok E (ss_regs ss) regs /\ facts_ok E (ss_facts ss) /\
mem_ok tfibsegs E (mrestrict (w_H W) (wbytes (ms_mem ms) (Z_to_bv 64 a) bs)) (ss_mem ss) /\
AI tfibsegs (w_H W) (w_A W) md' /\
same_but_materialized (with_fds (fd_insert (m_fds md) fd (FdFile pth (off + len_word bs)%bv)) md) md' /\
m_vmmaps md' = m_vmmaps md /\ eager_used md' = eager_used md /\
(forall i, 0 <= i < Z.of_nat (length bs) -> wbytes (ms_mem ms) (Z_to_bv 64 a) bs (Z_to_bv 64 (a + i)) = nth_error bs (Z.to_nat i)) /\
(forall x : word, bv_unsigned x < a \/ a + Z.of_nat (length bs) <= bv_unsigned x -> wbytes (ms_mem ms) (Z_to_bv 64 a) bs x = ms_mem ms x) /\
Z.of_nat (length bs) <= cnt).
Proof.
intros E ss ms W md fd pth off data bs a cnt HS Hrv H17 H10 H32 Hlk Hfs H11 H12 Hcnt Hbs Hck Hseg Ha0 Ha47.
destruct (st_ok_ecall_shape_r tfibsegs (w_H W) E ss ms HS Hrv) as (regs & mem & Hms & Hregs & Hmem & HG).
assert (Hlen : Z.of_nat (length bs) <= cnt).
{ rewrite <- Hbs. rewrite file_read_length. rewrite H12. lia. }
assert (HA : sv_denot E (sr_get (ss_regs ss) 11%bv) = Z_to_bv 64 a).
{ rewrite <- H11. rewrite Z_to_bv_bv_unsigned. reflexivity. }
assert (Hau : bv_unsigned (Z_to_bv 64 a) = a) by (apply u64_lit; lia).
assert (Hmsmem : mem = ms_mem ms) by (rewrite Hms; reflexivity).
destruct (read_dest_ok_w tfibsegs (ms_mem ms) (Z_to_bv 64 a) bs) as [w Hw].
{ intros i Hi. rewrite Hau. apply (seg_win_wview tfibsegs a 65536 (ms_mem ms)); [exact Hseg | lia | lia]. }
apply SRr_use_AI. intros HAI. cbn [cfg_model] in HAI.
destruct (node_read_file_lazy tfibsegs (w_H W) (w_A W) regs (Z_to_bv 64 (ss_pc ss)) (ms_mem ms) (seg_rom tfibsegs) md fd pth off data bs w
HAI) as (Hn & HAI' & Hs).
- rewrite (Hregs 17%bv). exact H17.
- rewrite (Hregs 10%bv). exact H10.
- exact H32.
- exact Hlk.
- exact Hfs.
- rewrite (Hregs 12%bv). unfold modeled_rw_count. apply Z.leb_le. rewrite H12.
etransitivity; [| apply Z.le_refl]. unfold rw_bytes_max. cbn. lia.
- rewrite (Hregs 12%bv). exact Hbs.
- rewrite (Hregs 11%bv), HA. exact Hw.
- rewrite (Hregs 11%bv), (Hregs 12%bv), HA, H12. unfold access_okb, TASK_SIZE. rewrite Hau.
apply andb_true_intro; split; apply Z.leb_le; lia.
- rewrite (Hregs 11%bv), HA. intros k Hk. unfold woff. rewrite Hau.
apply (seg_win_visible W a 65536); [exact Hseg | lia | lia | lia | lia].
- rewrite Hms. cbn [ms_mem pend_at]. rewrite <- ?Hmsmem in Hn. rewrite <- ?Hmsmem in Hs. rewrite <- ?Hmsmem in HAI'.
apply (SRr_node tfibsegs W _ unit _ tt _ Hn); [intros [] _; cbn [cfg_model]; exact HAI'|].
intros []. apply SRr_ret. split; [reflexivity|]. exists regs. eexists.
split; [reflexivity|].
assert (Hout : forall x : word, bv_unsigned x < a \/ a + Z.of_nat (length bs) <= bv_unsigned x -> wbytes mem (Z_to_bv 64 a) bs x = mem x).
{ intros x [Hx|Hx]; [apply wbytes_below; rewrite Hau; lia | apply wbytes_above; rewrite Hau; lia]. }
split.
{ rewrite read_mem_wbytes, (Hregs 11%bv), HA. reflexivity. }
rewrite (Hregs 11%bv), HA in HAI', Hs.
split; [exact Hregs|]. split; [exact HG|]. split.
{
apply (mem_ok_win tfibsegs E (mrestrict (w_H W) mem) _ (ss_mem ss) a 65536 Hmem Hck).
intros x Hx64 Hx. unfold mrestrict. destruct (w_H W (Z_to_bv 64 x)); [reflexivity|]. apply Hout. rewrite u64_lit by lia. lia. }
pose proof (same_but_materialized_frame _ _ Hs) as (_ & Hvm & Hlz & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Heu).
split; [destruct bs; exact HAI'|]. split; [destruct bs; exact Hs|].
split. { destruct bs; rewrite Hvm; destruct md; reflexivity. }
split. { destruct bs; rewrite Heu; unfold eager_used; destruct md; reflexivity. }
split; [| split; [exact Hout | exact Hlen]].
intros i Hi.
rewrite (wbytes_inside' bs mem (Z_to_bv 64 a) (Z_to_bv 64 (a + i))) by (rewrite ?Hau, ?u64_lit by lia; lia).
rewrite Hau, u64_lit by lia. replace (a + i - a) with i by lia. symmetry. apply nth_error_nth'. lia.
Qed.
Section f.
Variables (sp : word) (inp : ProcInput) (xw : nat -> word) (xd : nat -> list byte) (a0 p : list byte).
Hypothesis Hsp : valid_sp sp.
Hypothesis Hva : valid_argv [a0; p].
Hypothesis Hve : valid_envp (in_envp inp).
#[local] Notation EL := (YP08.E0 sp [a0; p] (in_envp inp) xw xd).
#[local] Notation usp := (bv_unsigned sp).
Let HWXi : wx_segs_nowrap tfibsegs := Hwx_tfa.
Definition eagree (E : YP0m.env) : Prop := (forall k, (k < K_M1)%nat -> ew E k = ew EL k) /\ ed E = ed EL.
Lemma eagree_0 : forall E, eagree E -> bv_unsigned (ew E 0) = usp.
Proof. intros E [HE _]. rewrite HE by (unfold K_M1; lia). reflexivity. Qed.
Lemma eagree_6 : forall E, eagree E -> usp <= bv_unsigned (ew E 6).
Proof.
intros E [HE _]. rewrite HE by (unfold K_M1; lia). change (ew EL 6) with (Z_to_bv 64 (z_rand usp [a0; p] (in_envp inp))).
pose proof (YP08.z_rand_end sp [a0; p] (in_envp inp) Hsp Hva Hve) as Hz. pose proof (u64_range sp).
unfold z_rand in *. rewrite u64_lit by lia. lia.
Qed.
Lemma eagree_ewset : forall E n v, eagree E -> (K_M1 <= n)%nat -> eagree (ewset E n v).
Proof. intros E n v [HE HD] Hn. split; [| exact HD]. intros k Hk. rewrite ew_ewset_other by lia. exact (HE k Hk). Qed.
Lemma eagree_havoc : forall E n ws, eagree E -> (K_M1 <= n)%nat -> eagree (havoc E n ws).
Proof. intros E n ws [HE HD] Hn. split; [| unfold havoc; cbn; exact HD]. intros k Hk. rewrite ew_havoc_old by lia. exact (HE k Hk). Qed.
Lemma winP : forall E ss msx (W : world tfibsegs),
(st_ok tfibsegs E ss (restrict (w_H W) msx) \/ st_ok_ecall tfibsegs E ss (restrict (w_H W) msx)) ->
bv_unsigned (ew E 0) = usp ->
(exists c1 c2 rest, ss_mem ss = YP09.mkRegion (Some 0%nat) (-65536) (-128) (-65536) (-128) c1
:: YP09.mkRegion (Some 0%nat) (-128) 0 (-128) 0 c2 :: rest) ->
forall a, usp - 65536 <= a < usp -> apresent (w_H W) (ms_mem msx) a.
Proof.
intros E ss msx W HSx E0x (c1 & c2 & rest & Hm) a Ha.
assert (HMx : mem_ok tfibsegs E (mrestrict (w_H W) (ms_mem msx)) (ss_mem ss)).
{ destruct HSx as [HSx|HSx]; [exact (st_ok_mem_ok tfibsegs E ss _ HSx) | destruct HSx as (_ & _ & _ & _ & _ & _ & _ & HM & _); exact HM]. }
rewrite Hm in HMx. destruct (Z.lt_ge_cases a (usp - 128)).
- eapply (win_present sp Hsp E (w_H W) (ms_mem msx)); [exact HMx | left; reflexivity | exact E0x | lia | lia | lia].
- eapply (win_present sp Hsp E (w_H W) (ms_mem msx)); [exact HMx | right; left; reflexivity | exact E0x | lia | lia | lia].
Qed.
Lemma add_rt : forall E ss (W : world tfibsegs) ms ly S md,
eagree E -> st_ok tfibsegs E ss (restrict (w_H W) ms) -> AR tfibsegs B ly S W (ms_mem ms) md ->
forallb (fun r1 => forallb (ext_chk r1) RT_REGIONS) (ss_mem ss) = true ->
st_ok tfibsegs E (with_rt ss) (restrict (w_H W) ms).
Proof.
intros E ss W ms ly S md HE HS HAR Hext. pose proof Hsp as (Ulo & Uhi & U16). pose proof (eagree_0 E HE) as E0'.
unfold with_rt. apply (st_ok_app_regions E ss (restrict (w_H W) ms) RT_REGIONS HS rt_wf).
- cbn [ms_mem restrict]. constructor; [apply (region_ok_const1 B HB E ly S W (ms_mem ms) md HAR)|].
constructor; [apply (region_ok_const2 B HB E ly S W (ms_mem ms) md HAR)|]. constructor; [apply region_ok_errno | constructor].
- cbn. unfold extent_disjoint. cbn. repeat split; lia.
- intros r1 r2 Hr1 Hr2.
pose proof (proj1 (forallb_forall _ _) Hext r1 Hr1) as X. pose proof (proj1 (forallb_forall _ _) X r2 Hr2) as Y. unfold ext_chk in Y.
pose proof (proj1 (forallb_forall _ _) rt_abs r2 Hr2) as Z2. cbn beta in Z2.
unfold extent_disjoint. destruct (r_base r2); [discriminate Z2|]. apply andb_prop in Z2 as [Z2a Z2b]. apply Z.leb_le in Z2a. apply Z.leb_le in Z2b.
destruct (r_base r1) as [[|n]|]; try discriminate Y; cbn [base_val].
+ apply Z.leb_le in Y. rewrite E0'. unfold sp_window_lo in Ulo. right. lia.
+ apply orb_prop in Y as [Y|Y]; apply Z.leb_le in Y; lia.
Qed.
Definition at_RW (E : YP0m.env) (W : world tfibsegs) (want : Z) (mem0 : word -> option byte) (md : Model) : world tfibsegs -> config -> Prop :=
fun W' c' => W' = W /\ exists ms' mat,
c' = mkCfg ms' (with_vm_backing (m_vm_lazy md) mat md)
/\ st_ok tfibsegs (ewset E A_WANT (Z_to_bv 64 want)) S_RW (restrict (w_H W) ms')
/\ frame_of E LH_mem mem0 (ms_mem ms')
/\ frame_of E LH_mem (mrestrict (w_H W) mem0) (mrestrict (w_H W) (ms_mem ms')).
Lemma U_want : forall E len cap, bv_unsigned (ew E A_LEN) = len -> bv_unsigned (ew E A_CAP) = cap -> 0 <= len <= cap -> cap <= 2 ^ 47 ->
U E sv_want = cap - len.
Proof.
intros E len cap E58 E59 Hlc Hcap. unfold sv_want. rewrite U_SAlu. cbn [zalu_raw]. rewrite U_SMd. cbn [zmd_raw]. rewrite !U_SOff, U_SLit, E58, E59, !Z.add_0_r.
rewrite (zcanon_id cap) by (unfold M64; lia). rewrite (zcanon_id len) by (unfold M64; lia).
unfold zcanon, M64. replace ((-1) mod 2 ^ 64) with (2 ^ 64 - 1) by reflexivity.
replace (len * (2 ^ 64 - 1)) with ((2 ^ 64 - len) + (len - 1) * 2 ^ 64) by lia. rewrite Z_mod_plus_full.
destruct (Z.eq_dec len 0) as [->|Hnz].
- rewrite Z.sub_0_r, Z_mod_same_full, Z.add_0_l, Z.sub_0_r. apply Z.mod_small. lia.
- rewrite (Z.mod_small (2 ^ 64 - len)) by lia.
replace (2 ^ 64 - len + cap) with ((cap - len) + 1 * 2 ^ 64) by lia. rewrite Z_mod_plus_full. apply Z.mod_small. lia.
Qed.
Lemma rd_to_RW : forall E (W : world tfibsegs) ms md len cap,
eagree E -> st_ok tfibsegs E S_RD (restrict (w_H W) ms) ->
bv_unsigned (ew E A_LEN) = len -> bv_unsigned (ew E A_CAP) = cap -> 0 <= len < cap -> cap <= 2 ^ 26 ->
SRr tfibsegs W (mkCfg ms md) (at_RW E W (Z.min (cap - len) 65536) (ms_mem ms) md).
Proof.
intros E W ms md len cap HE HS E58 E59 Hlen Hcap. pose proof HWXi as HWX.
pose proof (U_want E len cap E58 E59 ltac:(lia) ltac:(lia)) as Uw.
pose proof reabs_chk_RW as (CKa & CKb & OBL & Ma & Mb & _ & _ & AT77).
srr_run_with tfibtbl_lp_ok HS. rename HF into HF1. rename HFr into HFr1.
srr_branch_with tfibtbl_lp_ok HS.
-
rewrite branch_ltu_U in Hc. change (SAlu ALU_ADD (SMd M_MUL (SOff 58 0) (SLit (-1))) (SOff 59 0)) with sv_want in Hc. rewrite Uw, U_SLit in Hc. change (zcanon 65536) with 65536 in Hc. apply Z.ltb_lt in Hc.
srr_run_to_with tfibtbl_lp_ok HS RWPC.
apply SRr_ret. split; [reflexivity|].
lazymatch type of HS with st_ok _ _ _ (restrict _ ?msx) => exists msx end. eexists. split; [reflexivity|].
split.
+ rewrite Z.min_l by lia. unfold S_RW. rewrite <- (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 reabs_chk_RW)))))) at 1.
lazymatch type of HS with st_ok _ _ ?ssa ?msx =>
apply (st_ok_reabs tfibsegs LT77 E (ewset E A_WANT (Z_to_bv 64 (cap - len))) ssa msx RW_regs LH_mem RW_facts HS) end.
* split; [| intros d _; reflexivity]. intros n Hn. unfold LT77 in Hn. apply Nat.ltb_lt in Hn. rewrite ew_ewset_other by (unfold A_WANT; lia). reflexivity.
* exact CKa.
* apply Forall_forall. intros [r j] Hin. vm_compute in Hin. destruct Hin as [Heq|[]]. injection Heq as <- <-. cbn [fst snd ms_regs restrict].
rewrite ew_ewset_same.
lazymatch goal with |- _ = getr _ ?r => lazymatch type of HS with st_ok _ _ ?ss0 (restrict _ ?ms0) => rewrite (st_ok_restrict_reg tfibsegs (w_H W) E ss0 ms0 r HS) end end.
match goal with |- _ = sv_denot E ?v => let v' := eval vm_compute in v in change v with v' end.
change (SAlu ALU_ADD (SMd M_MUL (SOff 58 0) (SLit (-1))) (SOff 59 0)) with sv_want.
rewrite (denot_lit_U E sv_want), Uw. reflexivity.
* rewrite OBL. constructor; [| constructor]. cbn [fst snd]. unfold afact_ok, fact_want. cbn [af_lo af_hi af_al2].
rewrite ew_ewset_same, u64_lit by lia. rewrite Z.mod_1_r. repeat split; lia.
* cbn [ms_mem restrict]. rewrite <- Ma. apply (mem_ok_agree tfibsegs 77 E); [| rewrite Ma; exact AT77 | exact (st_ok_mem_ok tfibsegs _ _ _ HS)].
split; [| reflexivity]. intros n Hn. rewrite ew_ewset_other by (unfold A_WANT; lia). reflexivity.
+ pose proof skel_iter as (_ & _ & _ & _ & _ & _ & SKa & _).
split; [apply (frame_of_trans E LH_mem _ _ _ _ eq_refl HF1) | apply (frame_of_trans E LH_mem _ _ _ _ eq_refl HFr1)];
(eapply frame_of_skel'; [exact (eq_sym SKa) |]); [exact HF | exact HFr].
-
rewrite branch_ltu_U in Hc. change (SAlu ALU_ADD (SMd M_MUL (SOff 58 0) (SLit (-1))) (SOff 59 0)) with sv_want in Hc. rewrite Uw, U_SLit in Hc. change (zcanon 65536) with 65536 in Hc. apply Z.ltb_ge in Hc.
srr_run_to_with tfibtbl_lp_ok HS RWPC.
apply SRr_ret. split; [reflexivity|].
lazymatch type of HS with st_ok _ _ _ (restrict _ ?msx) => exists msx end. eexists. split; [reflexivity|].
split.
+ rewrite Z.min_r by lia. unfold S_RW. rewrite <- (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 reabs_chk_RW))))))) at 1.
lazymatch type of HS with st_ok _ _ ?ssb ?msx =>
apply (st_ok_reabs tfibsegs LT77 E (ewset E A_WANT (Z_to_bv 64 65536)) ssb msx RW_regs LH_mem RW_facts HS) end.
* split; [| intros d _; reflexivity]. intros n Hn. unfold LT77 in Hn. apply Nat.ltb_lt in Hn. rewrite ew_ewset_other by (unfold A_WANT; lia). reflexivity.
* exact CKb.
* apply Forall_forall. intros [r j] Hin. vm_compute in Hin. destruct Hin as [Heq|[]]. injection Heq as <- <-. cbn [fst snd ms_regs restrict].
rewrite ew_ewset_same.
lazymatch goal with |- _ = getr _ ?r => lazymatch type of HS with st_ok _ _ ?ss0 (restrict _ ?ms0) => rewrite (st_ok_restrict_reg tfibsegs (w_H W) E ss0 ms0 r HS) end end.
match goal with |- _ = sv_denot E ?v => let v' := eval vm_compute in v in change v with v' end. cbn [sv_denot]. reflexivity.
* rewrite OBL. constructor; [| constructor]. cbn [fst snd]. unfold afact_ok, fact_want. cbn [af_lo af_hi af_al2].
rewrite ew_ewset_same, u64_lit by lia. rewrite Z.mod_1_r. repeat split; lia.
* cbn [ms_mem restrict]. rewrite <- Mb. apply (mem_ok_agree tfibsegs 77 E); [| rewrite Mb; exact AT77 | exact (st_ok_mem_ok tfibsegs _ _ _ HS)].
split; [| reflexivity]. intros n Hn. rewrite ew_ewset_other by (unfold A_WANT; lia). reflexivity.
+ pose proof skel_iter as (_ & _ & _ & _ & _ & _ & _ & SKb).
split; [apply (frame_of_trans E LH_mem _ _ _ _ eq_refl HF1) | apply (frame_of_trans E LH_mem _ _ _ _ eq_refl HFr1)];
(eapply frame_of_skel'; [exact (eq_sym SKb) |]); [exact HF | exact HFr].
Qed.
Definition at_CHK (E : YP0m.env) (W : world tfibsegs) (n : Z) (mem1 : word -> option byte) (md1 : Model) : world tfibsegs -> config -> Prop :=
fun W' c' => W' = W /\ exists ms' mat,
c' = mkCfg ms' (with_vm_backing (m_vm_lazy md1) mat md1)
/\ st_ok tfibsegs (ewset E A_N (Z_to_bv 64 n)) S_CHK (restrict (w_H W) ms')
/\ frame_of (ewset E A_N (Z_to_bv 64 n)) (ss_mem S_RE) mem1 (ms_mem ms')
/\ frame_of (ewset E A_N (Z_to_bv 64 n)) (ss_mem S_RE) (mrestrict (w_H W) mem1) (mrestrict (w_H W) (ms_mem ms')).
Lemma ARmd_sbm : forall ly S W memx md0 md2 fds,
same_but_materialized (with_fds fds md0) md2 -> AR tfibsegs B ly S W memx md0 -> AR tfibsegs B ly S W memx md2.
Proof.
intros ly S W memx md0 md2 fds Hs HA.
apply (AR_same_but_materialized B ly S W memx (with_fds fds md0) md2); [| exact Hs]. apply AR_with_fds. exact HA.
Qed.
Lemma rd_step_pos : forall E (W : world tfibsegs) ms md ly S (pth : list byte) data (len cap want : Z),
eagree E -> st_ok tfibsegs E S_RW (restrict (w_H W) ms) ->
bv_unsigned (ew E A_LEN) = len -> bv_unsigned (ew E A_CAP) = cap -> bv_unsigned (ew E A_WANT) = want ->
AR tfibsegs B ly S W (ms_mem ms) md -> top_ok usp ly ->
0 <= len -> 1 <= want <= 65536 -> len + want <= cap -> cap <= 2 ^ 26 ->
m_fds md = APSG.fds3 (FdFile pth (Z_to_bv 64 len)) -> fs_lookup (m_fs md) pth = Some data -> len < Z.of_nat (length data) ->
let bs := file_read data (Z_to_bv 64 len) (Z_to_bv 64 want) in
let n := Z.of_nat (length bs) in
SRr tfibsegs W (mkCfg ms md)
(fun W' c' => exists mem0 md1,
let mem1 := wbytes mem0 (Z_to_bv 64 RS_LO) bs in
1 <= n <= want
/\ AI tfibsegs (w_H W) (w_A W) md1 /\ AR tfibsegs B ly S W mem1 md1
/\ m_fds md1 = APSG.fds3 (FdFile pth (Z_to_bv 64 (len + n))) /\ m_fs md1 = m_fs md
/\ (forall i, 0 <= i < n -> mem1 (Z_to_bv 64 (RS_LO + i)) = nth_error bs (Z.to_nat i))
/\ (forall x : word, bv_unsigned x < RS_LO \/ RS_LO + n <= bv_unsigned x -> mem1 x = mem0 x)
/\ frame_of E LH_mem (ms_mem ms) mem0
/\ frame_of E LH_mem (mrestrict (w_H W) (ms_mem ms)) (mrestrict (w_H W) mem0)
/\ at_CHK E W n mem1 md1 W' c').
Proof.
intros E W ms md ly S pth data len cap want HE HS E58 E59 E77 HAR HTOP Hlen0 Hwant Hlw Hcap Hfds Hfs Hdl bs n.
pose proof HWXi as HWX. pose proof Hsp as (Ulo & Uhi & U16). pose proof (u64_range sp) as Usp.
pose proof (u64_range (ew E A_LEN)) as R58. rewrite E58 in R58.
pose proof (eagree_0 E HE) as E0'. pose proof (top_ok_ceil _ _ HTOP) as HCT.
pose proof S_RE_shape as (_ & RErv & REat & _). pose proof skel_iter as (SK1 & SK2 & _).
pose proof (proj1 win_ok_iter) as WOK. pose proof (proj1 (proj2 win_ok_iter)) as WOKre.
assert (Hn : 1 <= n <= want).
{ subst n bs. rewrite file_read_length. rewrite !u64_lit by lia. lia. }
srr_run_with tfibtbl_lp_ok HS.
lazymatch type of HS with st_ok_ecall _ _ _ (restrict _ ?msx) => rename HS into HSE; set (ms1 := msx) in * end.
rename HF into HF1. rename HFr into HFr1.
pose proof (st_ok_ecall_shape_r tfibsegs (w_H W) E S_RE ms1 HSE eq_refl) as (rg & mm & Em & _ & HMM & _).
assert (Emm : ms_mem ms1 = mm) by (rewrite Em; reflexivity).
assert (Hwin1 : forall a, usp - 65536 <= a < usp -> apresent (w_H W) (ms_mem ms1) a).
{ apply (winP E S_RE ms1 W (or_intror HSE) E0'). do 3 eexists; reflexivity. }
assert (HAR1 : AR tfibsegs B ly S W (ms_mem ms1) (with_vm_backing (m_vm_lazy md) mat md)).
{ apply (AR_after_run B HB ARL ly S W E LH_mem (ms_mem ms) (ms_mem ms1) md mat HAR WOK); [rewrite E0'; exact Ulo | rewrite E0'; exact HCT | exact HF1 |].
rewrite E0'. intros a Ha. exact (apresent_some' _ _ _ (Hwin1 a Ha)). }
eapply SRr_bind.
{ apply (srr_read_win E S_RE ms1 W _ (Z_to_bv 64 3) pth (Z_to_bv 64 len) data bs RS_LO want HSE RErv).
- reflexivity.
- reflexivity.
- reflexivity.
- rewrite wvb_fds', Hfds. reflexivity.
- rewrite wvb_fs'. exact Hfs.
- reflexivity.
- eval_sr_get. cbn [sv_denot]. rewrite Z.add_0_r, Z_to_bv_bv_unsigned. exact E77.
- lia.
- subst bs. eval_sr_get. cbn [sv_denot]. rewrite Z.add_0_r, <- E77, !Z_to_bv_bv_unsigned. reflexivity.
- exact (proj1 rs_win_check).
- exact (proj2 rs_win_check).
- unfold RS_LO. lia.
- unfold RS_LO. lia. }
intros W1 c1 Hwle (-> & regs & md2 & Ems1 & -> & Hregs & HG & Hmem & HAI2 & Hs & Hvm & Heu & Hbytes' & Hfr' & Hlen').
assert (Hnw : len_word bs = Z_to_bv 64 n) by (unfold len_word; subst n; reflexivity).
pose proof (st_ok_resume_atom tfibsegs A_N fact_n E S_RE regs _ (len_word bs) Hregs Hmem HG REat
ltac:(rewrite Hnw; cbn; rewrite u64_lit by lia; lia) ltac:(cbn; lia) ltac:(cbn; rewrite Z.mod_1_r; reflexivity)) as HS2.
rewrite Hnw in HS2 |- *. rewrite <- restrict_mkst_fx in HS2.
pose proof (same_but_materialized_frame _ _ Hs) as (_ & _ & Hlz & _ & _ & _ & _ & _ & Hfds2 & _ & _ & Hfs2 & _ & _ & _ & _ & _).
assert (HAR2 : AR tfibsegs B ly S W (wbytes (ms_mem ms1) (Z_to_bv 64 RS_LO) bs) md2).
{ apply (AR_after_win_write ly S W (ms_mem ms1) (with_vm_backing (m_vm_lazy md) mat md) md2 RS_LO bs HAR1 ltac:(lia)
ltac:(unfold RS_LO, RS_HI; lia)).
- rewrite Hvm. destruct md; reflexivity.
- rewrite Hlz. destruct md; reflexivity.
- rewrite Heu. unfold eager_used. destruct md; reflexivity. }
assert (Hoff : (Z_to_bv 64 len + Z_to_bv 64 n)%bv = Z_to_bv 64 (len + n)).
{ apply bv_eq. rewrite bv_add_unsigned, !u64_lit by lia. unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64).
rewrite !Z.mod_small by lia. reflexivity. }
srr_run_to_with tfibtbl_lp_ok HS2 A_CHK.
apply SRr_ret. exists (ms_mem ms1), md2. cbv zeta.
split; [exact Hn|]. split; [exact HAI2|]. split; [exact HAR2|].
split. { rewrite Hfds2, with_fds_fds, wvb_fds', Hfds, Hnw, Hoff. unfold fd_insert, APSG.fds3. f_equal. }
split. { rewrite Hfs2, with_fds_fs, wvb_fs'. reflexivity. }
split; [exact Hbytes'|]. split; [intros x Hx; apply Hfr'; lia|].
split; [exact HF1|]. split; [exact HFr1|].
split; [reflexivity|]. eexists. eexists. split; [reflexivity|]. split; [exact HS2|]. split; [exact HF | exact HFr].
Qed.
Lemma rd_step_eof : forall E (W : world tfibsegs) ms md ly S (pth : list byte) data (len cap want : Z),
eagree E -> st_ok tfibsegs E S_RW (restrict (w_H W) ms) ->
bv_unsigned (ew E A_LEN) = len -> bv_unsigned (ew E A_CAP) = cap -> bv_unsigned (ew E A_WANT) = want ->
AR tfibsegs B ly S W (ms_mem ms) md -> top_ok usp ly ->
0 <= len -> 1 <= want <= 65536 ->
m_fds md = APSG.fds3 (FdFile pth (Z_to_bv 64 len)) -> fs_lookup (m_fs md) pth = Some data -> len = Z.of_nat (length data) ->
SRr tfibsegs W (mkCfg ms md)
(fun W' c' => W' = W /\ exists ms' md',
c' = mkCfg ms' md' /\ st_ok tfibsegs E S_HDR (restrict (w_H W) ms')
/\ AI tfibsegs (w_H W) (w_A W) md' /\ AR tfibsegs B ly S W (ms_mem ms') md'
/\ m_fds md' = APSG.fds_std /\ m_fs md' = m_fs md
/\ frame_of E LH_mem (ms_mem ms) (ms_mem ms')
/\ frame_of E LH_mem (mrestrict (w_H W) (ms_mem ms)) (mrestrict (w_H W) (ms_mem ms'))).
Proof.
intros E W ms md ly S pth data len cap want HE HS E58 E59 E77 HAR HTOP Hlen0 Hwant Hfds Hfs Hdl.
pose proof HWXi as HWX. pose proof Hsp as (Ulo & Uhi & U16). pose proof (u64_range sp) as Usp.
pose proof (u64_range (ew E A_LEN)) as R58. rewrite E58 in R58.
pose proof (eagree_0 E HE) as E0'. pose proof (top_ok_ceil _ _ HTOP) as HCT.
pose proof S_RE_shape as (_ & RErv & REat & _). pose proof skel_iter as (SK1 & SK2 & SK3 & SK4 & SK5 & SK6 & _).
pose proof win_ok_iter as (WOK & WOKre & _ & _ & WOKcl).
set (bs := file_read data (Z_to_bv 64 len) (Z_to_bv 64 want)).
assert (Hbs0 : bs = []) by (subst bs; apply file_read_eof; rewrite u64_lit by lia; lia).
srr_run_with tfibtbl_lp_ok HS.
lazymatch type of HS with st_ok_ecall _ _ _ (restrict _ ?msx) => rename HS into HSE; set (ms1 := msx) in * end.
rename HF into HF1. rename HFr into HFr1.
assert (HAR1 : AR tfibsegs B ly S W (ms_mem ms1) (with_vm_backing (m_vm_lazy md) mat md)).
{ apply (AR_after_run B HB ARL ly S W E LH_mem (ms_mem ms) (ms_mem ms1) md mat HAR WOK); [rewrite E0'; exact Ulo | rewrite E0'; exact HCT | exact HF1 |].
rewrite E0'. intros a Ha. apply (apresent_some' (w_H W)). apply (winP E S_RE ms1 W (or_intror HSE) E0'); [| exact Ha]. do 3 eexists; reflexivity. }
eapply SRr_bind.
{ apply (srr_read_win E S_RE ms1 W _ (Z_to_bv 64 3) pth (Z_to_bv 64 len) data bs RS_LO want HSE RErv).
- reflexivity.
- reflexivity.
- reflexivity.
- rewrite wvb_fds', Hfds. reflexivity.
- rewrite wvb_fs'. exact Hfs.
- reflexivity.
- eval_sr_get. cbn [sv_denot]. rewrite Z.add_0_r, Z_to_bv_bv_unsigned. exact E77.
- lia.
- subst bs. eval_sr_get. cbn [sv_denot]. rewrite Z.add_0_r, <- E77, !Z_to_bv_bv_unsigned. reflexivity.
- exact (proj1 rs_win_check).
- exact (proj2 rs_win_check).
- unfold RS_LO. lia.
- unfold RS_LO. lia. }
intros W1 c1 Hwle (-> & regs & md2 & Ems1 & -> & Hregs & HG & Hmem & HAI2 & Hs & Hvm & Heu & _ & _ & _).
rewrite Hbs0 in *. cbn [wbytes len_word length Z.of_nat] in *.
pose proof (same_but_materialized_frame _ _ Hs) as (_ & _ & Hlz & _ & _ & _ & _ & _ & Hfds2 & _ & _ & Hfs2 & _ & _ & _ & _ & _).
assert (ARmd2 : forall memx, AR tfibsegs B ly S W memx (with_vm_backing (m_vm_lazy md) mat md) -> AR tfibsegs B ly S W memx md2).
{ intros memx HA. apply (AR_model_same B ly S W memx (with_vm_backing (m_vm_lazy md) mat md) md2 HA).
- rewrite Hvm. destruct md; reflexivity.
- rewrite Hlz. destruct md; reflexivity.
- rewrite Heu. unfold eager_used. destruct md; reflexivity. }
pose proof (st_ok_resume_sv tfibsegs E S_RE regs (mrestrict (w_H W) (ms_mem ms1)) (SLit 0) (Z_to_bv 64 0) Hregs Hmem HG eq_refl) as HS2.
rewrite <- restrict_mkst_fx in HS2. change (Z_to_bv 64 (Z.of_nat 0)) with (Z_to_bv 64 0).
srr_run_with tfibtbl_lp_ok HS2.
lazymatch type of HS2 with st_ok_ecall _ _ _ (restrict _ ?msx) => rename HS2 into HSC; set (msB := msx) in * end.
rename HF into HF2. rename HFr into HFr2.
pose proof (st_ok_ecall_shape_r tfibsegs (w_H W) E _ msB HSC eq_refl) as (regs2 & mem2 & Em2 & Hregs2 & Hmem2 & HG2).
assert (HAR3 : AR tfibsegs B ly S W (ms_mem msB) (with_vm_backing (m_vm_lazy md2) mat0 md2)).
{ apply (AR_after_run B HB ARL ly S W E (ss_mem S_RE) (ms_mem ms1) (ms_mem msB) md2 mat0 (ARmd2 _ HAR1) WOKre);
[rewrite E0'; exact Ulo | rewrite E0'; exact HCT | exact HF2 |].
rewrite E0'. intros a Ha. apply (apresent_some' (w_H W)). apply (winP E _ msB W (or_intror HSC) E0'); [| exact Ha]. do 3 eexists; reflexivity. }
apply SRr_use_AI. intros HAI3. cbn [cfg_model] in HAI3. rewrite Em2.
destruct (node_close_lazy tfibsegs (w_H W) (w_A W) regs2 (Z_to_bv 64 (ss_pc S_CL)) mem2 (seg_rom tfibsegs) (with_vm_backing (m_vm_lazy md2) mat0 md2)
(Z_to_bv 64 3) (FdFile pth (Z_to_bv 64 len + Z_to_bv 64 0)%bv) HAI3) as [Hn3 HAI4].
{ rewrite (Hregs2 17%bv). reflexivity. }
{ rewrite (Hregs2 10%bv). reflexivity. }
{ reflexivity. }
{ rewrite wvb_fds', Hfds2, with_fds_fds, wvb_fds', Hfds. unfold fd_insert, APSG.fds3. cbn -[Z_to_bv bv_add]. reflexivity. }
apply (SRr_node tfibsegs W _ unit _ tt _ Hn3); [intros [] _; exact HAI4|]. intros [].
pose proof (st_ok_resume_sv tfibsegs E S_CL regs2 (mrestrict (w_H W) mem2) (SLit 0) (Z_to_bv 64 0) Hregs2 Hmem2 HG2 eq_refl) as HS4.
rewrite <- restrict_mkst_fx in HS4.
srr_run_with tfibtbl_lp_ok HS4.
apply SRr_use_AI. intros HAI5. cbn [cfg_model] in HAI5.
apply SRr_ret. split; [reflexivity|]. eexists. eexists. split; [reflexivity|]. split; [exact HS4|].
assert (Emem2 : ms_mem msB = mem2) by (rewrite Em2; reflexivity).
split; [exact HAI5|].
split.
{ apply (AR_after_run B HB ARL ly S W E (ss_mem S_CL) mem2 _ _ _ (AR_with_fds B ly S W mem2 _ _ ltac:(rewrite <- Emem2; exact HAR3)) WOKcl);
[rewrite E0'; exact Ulo | rewrite E0'; exact HCT | exact HF |].
rewrite E0'. intros a Ha. apply (apresent_some' (w_H W)). apply (winP E S_HDR _ W (or_introl HS4) E0'); [| exact Ha]. do 3 eexists; reflexivity. }
split. { rewrite wvb_fds', with_fds_fds, wvb_fds', Hfds2, with_fds_fds, wvb_fds', Hfds. unfold fd_remove, fd_insert, APSG.fds3, APSG.fds_std. cbn -[Z_to_bv bv_add]. reflexivity. }
split. { rewrite wvb_fs', with_fds_fs, wvb_fs', Hfs2, with_fds_fs, wvb_fs'. reflexivity. }
split.
- apply (frame_of_trans E LH_mem (ss_mem S_RE) _ _ _ (eq_sym SK1) HF1).
apply (frame_of_trans E (ss_mem S_RE) (ss_mem S_CL) _ _ _ ltac:(rewrite SK1, SK5; reflexivity) HF2). rewrite Emem2. exact HF.
- apply (frame_of_trans E LH_mem (ss_mem S_RE) _ _ _ (eq_sym SK1) HFr1).
apply (frame_of_trans E (ss_mem S_RE) (ss_mem S_CL) _ _ _ ltac:(rewrite SK1, SK5; reflexivity) HFr2). rewrite Emem2. exact HFr.
Qed.
Lemma errno_EISDIR : errno_ret EISDIR = Z_to_bv 64 (2 ^ 64 - 21). Proof. apply bv_eq. vm_compute. reflexivity. Qed.
Lemma rd_dir : forall E (W : world tfibsegs) ms md ly S (want : Z),
eagree E -> st_ok tfibsegs E S_RW (restrict (w_H W) ms) ->
bv_unsigned (ew E A_WANT) = want -> 1 <= want <= 65536 ->
AR tfibsegs B ly S W (ms_mem ms) md -> top_ok usp ly ->
m_fds md = APSG.fds3 FdDir ->
SRr tfibsegs W (mkCfg ms md)
(fun W' c' => W' = W /\ exists ms' md',
c' = mkCfg ms' md' /\ st_ok tfibsegs E S_DIR (restrict (w_H W) ms')
/\ AI tfibsegs (w_H W) (w_A W) md' /\ AR tfibsegs B ly S W (ms_mem ms') md'
/\ m_fds md' = m_fds md /\ m_fs md' = m_fs md
/\ frame_of E LH_mem (ms_mem ms) (ms_mem ms')
/\ frame_of E LH_mem (mrestrict (w_H W) (ms_mem ms)) (mrestrict (w_H W) (ms_mem ms'))).
Proof.
intros E W ms md ly S want HE HS E77 Hwant HAR HTOP Hfds.
pose proof HWXi as HWX. pose proof Hsp as (Ulo & Uhi & U16). pose proof (u64_range sp) as Usp.
pose proof (eagree_0 E HE) as E0'. pose proof (top_ok_ceil _ _ HTOP) as HCT.
pose proof S_RE_shape as (_ & RErv & REat & _). pose proof skel_iter as (SK1 & _).
pose proof win_ok_iter as (WOK & WOKre & _). pose proof S_DIR_facts as (_ & _ & _ & _ & _ & _ & _ & SKd).
srr_run_with tfibtbl_lp_ok HS.
lazymatch type of HS with st_ok_ecall _ _ _ (restrict _ ?msx) => rename HS into HSE; set (ms1 := msx) in * end.
rename HF into HF1. rename HFr into HFr1.
assert (HAR1 : AR tfibsegs B ly S W (ms_mem ms1) (with_vm_backing (m_vm_lazy md) mat md)).
{ apply (AR_after_run B HB ARL ly S W E LH_mem (ms_mem ms) (ms_mem ms1) md mat HAR WOK); [rewrite E0'; exact Ulo | rewrite E0'; exact HCT | exact HF1 |].
rewrite E0'. intros a Ha. apply (apresent_some' (w_H W)). apply (winP E S_RE ms1 W (or_intror HSE) E0'); [| exact Ha]. do 3 eexists; reflexivity. }
pose proof (st_ok_ecall_shape_r tfibsegs (w_H W) E _ ms1 HSE eq_refl) as (regs & mem & Em & Hregs & Hmem & HG).
apply SRr_use_AI. intros HAI1. cbn [cfg_model] in HAI1. rewrite Em.
destruct (node_read_dir_lazy tfibsegs (w_H W) (w_A W) regs (Z_to_bv 64 (ss_pc S_RE)) mem (seg_rom tfibsegs) (with_vm_backing (m_vm_lazy md) mat md)
(Z_to_bv 64 3) HAI1) as [Hn HAI2].
{ rewrite (Hregs 17%bv). reflexivity. }
{ rewrite (Hregs 10%bv). reflexivity. }
{ reflexivity. }
{ rewrite wvb_fds', Hfds. reflexivity. }
{ pose proof E77 as E77'. unfold A_WANT in E77'.
rewrite (Hregs 11%bv), (Hregs 12%bv). eval_sr_get. cbn [sv_denot]. rewrite !Z.add_0_r, E77'.
unfold access_okb, TASK_SIZE, RS_LO. rewrite !u64_lit by lia. apply andb_true_intro; split; apply Z.leb_le; lia. }
apply (SRr_node tfibsegs W _ unit _ tt _ Hn); [intros [] _; exact HAI2|]. intros [].
pose proof (st_ok_resume_sv tfibsegs E S_RE regs (mrestrict (w_H W) mem) (SLit (2 ^ 64 - 21)) (errno_ret EISDIR) Hregs Hmem HG
ltac:(rewrite errno_EISDIR; reflexivity)) as HS2.
rewrite <- restrict_mkst_fx in HS2.
assert (Emm : mem = ms_mem ms1) by (rewrite Em; reflexivity).
srr_run_with tfibtbl_lp_ok HS2.
apply SRr_use_AI. intros HAI3. cbn [cfg_model] in HAI3.
apply SRr_ret. split; [reflexivity|]. eexists. eexists. split; [reflexivity|]. split; [exact HS2|].
split; [exact HAI3|].
split.
{ apply (AR_after_run B HB ARL ly S W E (ss_mem S_RE) mem _ _ _ ltac:(rewrite Emm; exact HAR1) WOKre); [rewrite E0'; exact Ulo | rewrite E0'; exact HCT | exact HF |].
rewrite E0'. intros a Ha. apply (apresent_some' (w_H W)). apply (winP E S_DIR _ W (or_introl HS2) E0'); [| exact Ha]. do 3 eexists; reflexivity. }
split; [rewrite ?wvb_fds'; reflexivity|]. split; [rewrite ?wvb_fs'; reflexivity|].
split.
- apply (frame_of_trans E LH_mem (ss_mem S_RE) _ _ _ (eq_sym SK1) HF1). rewrite <- Emm. exact HF.
- apply (frame_of_trans E LH_mem (ss_mem S_RE) _ _ _ (eq_sym SK1) HFr1). rewrite <- Emm. exact HFr.
Qed.
Lemma rs_zero_shadow : forall ly S W mem md, AR tfibsegs B ly S W mem md ->
zero_shadow (aview tfibsegs (w_H W) mem) SHADOW_OFF 0xa2930 (0x5fb000 - 0xa2930).
Proof.
intros ly S W mem md HAR.
apply (al_zshadow _ _ ARL ly S W mem md (0xa2930, 0x5fb000 - 0xa2930) HAR).
unfold zero_shadow_ranges. right. rewrite (ts_zsh B HB). unfold Tfib_zero_shadow. cbn. tauto.
Qed.
Lemma rs_range_addressable : forall ly S W mem md n, AR tfibsegs B ly S W mem md -> 0 <= n -> RS_LO + n <= RS_HI ->
range_addressable (aview tfibsegs (w_H W) mem) SHADOW_OFF RS_LO n.
Proof.
intros ly S W mem md n HAR Hn Hle x Hx.
apply (zero_shadow_range _ SHADOW_OFF 0xa2930 (0x5fb000 - 0xa2930) eq_refl eq_refl (rs_zero_shadow ly S W mem md HAR) x).
unfold RS_LO, RS_HI in *. lia.
Qed.
Lemma rs_shadow_hull_vis : forall ly S W mem md n, AR tfibsegs B ly S W mem md -> 0 < n -> RS_LO + n <= RS_HI ->
shadow_hull_vis (aview tfibsegs (w_H W) mem) RS_LO n.
Proof.
intros ly S W mem md n HAR Hn Hle s Hs. pose proof (rs_zero_shadow ly S W mem md HAR) as Z0.
replace s with (shadow_of_addr SHADOW_OFF 0xa2930 + (s - shadow_of_addr SHADOW_OFF 0xa2930)) by lia.
rewrite Z0; [discriminate|].
unfold shadow_addr, shadow_of_addr, SHADOW_OFF, RS_LO, RS_HI in *. lia.
Qed.
Lemma rd_chk : forall E (W : world tfibsegs) ms md ly S (n len cap : Z),
read_check_tfa B ->
let E2 := ewset E A_N (Z_to_bv 64 n) in
eagree E -> st_ok tfibsegs E2 S_CHK (restrict (w_H W) ms) ->
AR tfibsegs B ly S W (ms_mem ms) md -> top_ok usp ly -> 1 <= n <= 65536 ->
SRr tfibsegs W (mkCfg ms md)
(fun W' c' => W' = W /\ exists regs' mem' md',
c' = mkCfg (mkst regs' (Z_to_bv 64 A_CHK_END) mem' (seg_rom tfibsegs)) md'
/\ st_ok tfibsegs (havoc E2 K_CHK (map (getr regs') CLOB_CHK)) S_CHK' (restrict (w_H W) (mkst regs' (Z_to_bv 64 A_CHK_END) mem' (seg_rom tfibsegs)))
/\ AR tfibsegs B ly S W mem' md'
/\ same_but_materialized md md'
/\ (forall a, 0 <= a < 2 ^ 64 -> ~ (usp + ICPT_SP - ESTACK <= a < usp + ICPT_SP) -> aview tfibsegs (w_H W) mem' a = aview tfibsegs (w_H W) (ms_mem ms) a)
/\ (forall a, apresent (w_H W) (ms_mem ms) a -> apresent (w_H W) mem' a)).
Proof.
intros E W ms md ly S n len cap RCHK E2 HE HS HAR HTOP Hn.
pose proof Hsp as (Ulo & Uhi & U16). pose proof (u64_range sp) as Usp.
assert (E2_0 : bv_unsigned (ew E2 0) = usp) by (subst E2; rewrite ew_ewset_other by (unfold A_N; lia); exact (eagree_0 E HE)).
pose proof (st_ok_restrict_mkst tfibsegs (w_H W) E2 S_CHK ms HS eq_refl) as Hshape.
set (regs := ms_regs ms) in *. set (mem := ms_mem ms) in *.
assert (R1 : getr regs 1%bv = w64 0x4366c) by (rewrite (st_ok_restrict_reg tfibsegs (w_H W) E2 S_CHK ms 1%bv HS); reflexivity).
assert (R3 : getr regs 3%bv = w64 TFIB_GP) by (rewrite (st_ok_restrict_reg tfibsegs (w_H W) E2 S_CHK ms 3%bv HS); reflexivity).
assert (R4 : getr regs 4%bv = w64 TFIB_TP) by (rewrite (st_ok_restrict_reg tfibsegs (w_H W) E2 S_CHK ms 4%bv HS); reflexivity).
assert (R2 : getr regs 2%bv = Z_to_bv 64 (usp + ICPT_SP)).
{ rewrite (st_ok_restrict_reg tfibsegs (w_H W) E2 S_CHK ms 2%bv HS). eval_sr_get. cbn [sv_denot]. rewrite E2_0. reflexivity. }
assert (R10 : getr regs 10%bv = w64 n).
{ rewrite (st_ok_restrict_reg tfibsegs (w_H W) E2 S_CHK ms 10%bv HS). eval_sr_get. cbn [sv_denot]. subst E2. unfold A_N. rewrite ew_ewset_same, u64_lit by lia. rewrite Z.add_0_r. reflexivity. }
assert (R9 : getr regs 9%bv = w64 RS_LO) by (rewrite (st_ok_restrict_reg tfibsegs (w_H W) E2 S_CHK ms 9%bv HS); reflexivity).
assert (Hsp' : spZ regs = usp + ICPT_SP) by (unfold spZ; rewrite R2; unfold ICPT_SP; rewrite u64_lit by (unfold sp_window_lo in Ulo; lia); lia).
pose proof (st_ok_mem_ok tfibsegs E2 S_CHK _ HS) as HM. cbn [restrict ms_mem] in HM. fold mem in HM.
assert (Hwin : forall a, usp - 65536 <= a < usp - 128 -> apresent (w_H W) mem a).
{ intros a Ha. eapply (win_present sp Hsp E2 (w_H W) mem (ss_mem S_CHK)); [exact HM | left; reflexivity | exact E2_0 | lia | lia | cbn; lia]. }
rewrite Hshape. change (Z_to_bv 64 (ss_pc S_CHK)) with (w64 A_CHK). fold regs mem.
change (mkCfg (mkst regs (w64 A_CHK) mem (seg_rom tfibsegs)) md) with (cfg_at tfibsegs A_CHK regs mem md).
eapply SRr_mono.
{ apply (RCHK ly S W regs mem md n RS_LO).
- split; [exact HAR|]. split; [unfold top_ok in *; tauto|]. split; [rewrite R1; unfold YK0s.ret_ok; apply bv_eq; vm_compute; reflexivity|].
split; [rewrite Hsp'; unfold ICPT_SP; replace (usp + (-128 - 2128)) with (usp + (-141) * 16) by lia; rewrite Z.mod_add by lia; exact U16|].
split; [rewrite Hsp'; unfold ICPT_SP, sp_window_lo in *; lia|]. split; [rewrite Hsp'; unfold top_ok, ICPT_SP in *; lia|].
split; [rewrite Hsp'; intros a Ha; apply Hwin; unfold ESTACK, ICPT_SP in Ha; lia|].
split; [rewrite (ts_gp B HB); exact R3 | rewrite (ts_tp B HB); exact R4].
- exact R10.
- exact R9.
- lia.
- unfold RS_LO; lia.
- unfold RS_LO; lia.
- left. unfold RS_LO, kLowMemEnd. lia.
- apply (rs_range_addressable ly S W mem md n HAR); [lia | unfold RS_LO, RS_HI; lia].
- apply (rs_shadow_hull_vis ly S W mem md n HAR); [lia | unfold RS_LO, RS_HI; lia]. }
cbv beta. intros W' c' _ (-> & regs' & mem' & md' & -> & HAR' & HP & Hs & Ha0 & Hfr & Hpres).
split; [reflexivity|]. exists regs', mem', md'. split; [reflexivity|].
rewrite Hshape, restrict_mkst_fx in HS. fold regs mem in HS.
assert (HST : st_ok tfibsegs (havoc E2 K_CHK (map (getr regs') CLOB_CHK)) S_CHK'
(mkst regs' (Z_to_bv 64 A_CHK_END) (mrestrict (w_H W) mem') (seg_rom tfibsegs))).
{ unfold S_CHK'.
apply (st_ok_splice_havoc tfibsegs K_CHK E2 S_CHK regs regs' (w64 A_CHK) A_CHK_END (mrestrict (w_H W) mem) (mrestrict (w_H W) mem')
_ [(10%bv : bv 5, SOff A_N 0)] CLOB_CHK HS).
- vm_compute. reflexivity.
- vm_compute. reflexivity.
- vm_compute. reflexivity.
- vm_compute. reflexivity.
- vm_compute. reflexivity.
- exact (regs_kept_CHK regs regs' HP).
- constructor; [| constructor]. cbn [fst snd]. split; [reflexivity|]. rewrite Ha0. cbn [sv_denot]. subst E2. unfold A_N. rewrite ew_ewset_same, u64_lit by lia. rewrite Z.add_0_r. reflexivity.
-
assert (SCR : forall a, 0 <= a < 2 ^ 64 -> ~ (usp + ICPT_SP - ESTACK <= a < usp + ICPT_SP) ->
mbyte tfibsegs (mrestrict (w_H W) mem') a = mbyte tfibsegs (mrestrict (w_H W) mem) a).
{ intros a HaR Ha. apply (mbyte_of_aview tfibsegs). apply Hfr; [exact HaR | rewrite Hsp'; exact Ha]. }
destruct HM as (Hwf & Hok & Hpd).
split; [vm_compute; reflexivity|]. split.
+ pose proof (Forall_inv Hok) as Hr0. pose proof (Forall_inv_tail Hok) as Hrs0.
change (ss_mem S_CHK') with (hd R_errno (ss_mem S_CHK') :: tl (ss_mem S_CHK')). constructor.
*
apply (region_ok_transport_chunks E2 (mrestrict (w_H W) mem) (mrestrict (w_H W) mem')).
-- eapply region_ok_sub; [| cbn; lia | exact Hr0]. repeat split; cbn; try lia. intros c Hc. cbn in Hc |- *. tauto.
-- intros c i Hc Hi. cbn [r_base base_val]. rewrite E2_0. cbn [r_chunks hd] in Hc. unfold sp_window_lo, sp_window_hi in Ulo, Uhi.
repeat (destruct Hc as [<-|Hc]; [cbn in Hi |- *; apply SCR; unfold ESTACK, ICPT_SP; lia|]). destruct Hc.
-- cbn [r_wlo r_whi r_base base_val]. rewrite E2_0. intros o Ho. apply (apresent_writable tfibsegs). apply Hpres. apply Hwin. lia.
*
change (tl (ss_mem S_CHK')) with (tl (ss_mem S_CHK)).
assert (HMt : mem_ok tfibsegs E2 (mrestrict (w_H W) mem) (tl (ss_mem S_CHK))).
{ split; [vm_compute; reflexivity|]. split; [exact Hrs0 | exact (proj2 Hpd)]. }
assert (TAIL : forallb (fun r => match r_base r with Some 0%nat => (-128 <=? r_lo r) | Some _ => false
| None => (0 <=? r_lo r) && (r_hi r <=? 0x5fb000) end)%bool (tl (ss_mem S_CHK)) = true) by (vm_compute; reflexivity).
assert (HK : Forall (region_kept tfibsegs E2 (mrestrict (w_H W) mem) (mrestrict (w_H W) mem')) (tl (ss_mem S_CHK))).
{ apply Forall_forall. intros r Hr.
pose proof (proj1 (forallb_forall _ _) TAIL r Hr) as Hc. cbn beta in Hc.
pose proof (proj1 (Forall_forall _ _) Hrs0 r Hr) as (B1 & B2 & _).
assert (OFF : forall a, base_val E2 (r_base r) + r_lo r <= a < base_val E2 (r_base r) + r_hi r -> ~ (usp + ICPT_SP - ESTACK <= a < usp + ICPT_SP)).
{ intros a Ha. destruct (r_base r) as [[|k]|]; try discriminate Hc; cbn [base_val] in Ha, B1, B2.
- apply Z.leb_le in Hc. rewrite E2_0 in Ha. unfold ESTACK, ICPT_SP. lia.
- apply andb_prop in Hc as [Hc1 Hc2]. apply Z.leb_le in Hc1. apply Z.leb_le in Hc2. unfold ESTACK, ICPT_SP, sp_window_lo in *. lia. }
split; intros a Ha; [apply SCR; [lia | apply OFF; exact Ha]|].
intros Hw. exact (wview_grows tfibsegs _ _ _ (mem_grows_of_apresent (w_H W) mem mem' Hpres) Hw). }
exact (proj1 (proj2 (mem_ok_kept tfibsegs E2 _ (mrestrict (w_H W) mem') (tl (ss_mem S_CHK)) HMt ltac:(vm_compute; reflexivity) HK))).
+ apply (pairwise_disjoint_extents E2 (ss_mem S_CHK) (ss_mem S_CHK')); [vm_compute; reflexivity | exact Hpd]. }
rewrite <- restrict_mkst_fx in HST. split; [exact HST|]. split; [exact HAR'|]. split; [exact Hs|].
split; [intros a HaR Ha; apply Hfr; [exact HaR | rewrite Hsp'; exact Ha] | exact Hpres].
Qed.
Definition at_st (ss ss' : sstate) (E : YP0m.env) (W : world tfibsegs) (mem0 : word -> option byte) (md : Model) : world tfibsegs -> config -> Prop :=
fun W' c' => W' = W /\ exists ms' mat,
c' = mkCfg ms' (with_vm_backing (m_vm_lazy md) mat md)
/\ st_ok tfibsegs E ss' (restrict (w_H W) ms')
/\ frame_of E (ss_mem ss) mem0 (ms_mem ms')
/\ frame_of E (ss_mem ss) (mrestrict (w_H W) mem0) (mrestrict (w_H W) (ms_mem ms')).
Lemma cp_run : forall E3 (W : world tfibsegs) regs mem md,
st_ok tfibsegs E3 S_CHK' (restrict (w_H W) (mkst regs (Z_to_bv 64 A_CHK_END) mem (seg_rom tfibsegs))) ->
SRr tfibsegs W (mkCfg (mkst regs (Z_to_bv 64 A_CHK_END) mem (seg_rom tfibsegs)) md) (at_st S_CHK' S_CP E3 W mem md).
Proof.
intros E3 W regs mem md HS. pose proof HWXi as HWX.
srr_run_to_with tfibtbl_lp_ok HS A_icpt_memcpy.
apply SRr_ret. split; [reflexivity|].
lazymatch type of HS with st_ok _ _ _ (restrict _ ?msx) => exists msx end. eexists. split; [reflexivity|].
split; [exact HS|]. split; [exact HF | exact HFr].
Qed.
Lemma tfib_segs_low : forall a, in_img tfibsegs a -> 0 <= a < kLowMemEnd.
Proof.
intros a Hi. unfold kLowMemEnd. destruct (Z.lt_ge_cases a 0x5fb000) as [Hl|Hge].
- destruct (Z.lt_ge_cases a 0) as [Hn|]; [|lia]. exfalso. destruct Hi as (sg & Hin & Hr). rewrite tfib_segs_eq in Hin.
destruct Hin as [<-|[<-|[<-|[<-|[]]]]]; cbn in Hr; lia.
- exfalso. exact (not_in_img_high a Hge Hi).
Qed.
Lemma restrict_of_aview : forall (H : word -> bool) (m m' : word -> option byte) a,
0 <= a < 2 ^ 64 -> ~ in_img tfibsegs a ->
aview tfibsegs H m' a = aview tfibsegs H m a -> mrestrict H m' (Z_to_bv 64 a) = mrestrict H m (Z_to_bv 64 a).
Proof.
intros H m m' a Ha Hn X. unfold aview, mbyte in X. rewrite (seg_rom_none tfibsegs a Ha Hn) in X.
destruct (mrestrict H m' (Z_to_bv 64 a)) as [b'|], (mrestrict H m (Z_to_bv 64 a)) as [b|]; cbn in X; try discriminate X; [| reflexivity].
injection X as X. f_equal. apply bv_eq. exact X.
Qed.
Lemma restrict_some_of_aview : forall (H : word -> bool) (m' : word -> option byte) a (b : byte),
0 <= a < 2 ^ 64 -> ~ in_img tfibsegs a ->
aview tfibsegs H m' a = Some (bv_unsigned b) -> mrestrict H m' (Z_to_bv 64 a) = Some b.
Proof.
intros H m' a b Ha Hn X. unfold aview, mbyte in X. rewrite (seg_rom_none tfibsegs a Ha Hn) in X.
destruct (mrestrict H m' (Z_to_bv 64 a)) as [b'|]; cbn in X; [| discriminate X]. injection X as X. f_equal. apply bv_eq. exact X.
Qed.
Lemma range_addressable_of_block' : forall ly S W mem md q m a n,
AR tfibsegs B ly S W mem md -> In (q, m) (ablocks B ly S) -> q <= a -> a + n <= q + req_size m ->
range_addressable (aview tfibsegs (w_H W) mem) SHADOW_OFF a n.
Proof.
intros ly S W mem md q m a n HAR Hin Hpa Han.
destruct (al_shadow _ _ ARL ly S W mem md q m HAR Hin) as [Hbs _].
destruct (Z_lt_le_dec 0 n); [|apply range_addressable_nil; lia].
eapply block_shadow_range; [exact Hbs | lia | lia].
Qed.
Lemma shadow_hull_vis_of_block' : forall ly S W mem md q m d n,
AR tfibsegs B ly S W mem md -> In (q, m) (ablocks B ly S) -> q <= d -> d + n <= q + req_size m -> 0 < n ->
shadow_hull_vis (aview tfibsegs (w_H W) mem) d n.
Proof.
intros ly S W mem md q m d n HAR Hin Hpd Hdn Hn s Hs.
destruct (al_shadow _ _ ARL ly S W mem md q m HAR Hin) as [_ Hh]. apply Hh.
pose proof (shadow_mono q d Hpd) as M1. pose proof (shadow_mono (d + n - 1) (q + req_size m - 1) ltac:(lia)) as M2.
assert (R8 : forall u v, u <= v -> u / 8 * 8 <= v / 8 * 8) by (intros u v Huv; apply Z.mul_le_mono_nonneg_r; [lia|]; apply Z.div_le_mono; lia).
pose proof (R8 _ _ M1). pose proof (R8 _ _ M2). lia.
Qed.
Lemma rd_cpy : forall E3 (W : world tfibsegs) ms md ly S (pb : sptr) (n buf len cap : Z) (data bs : list byte),
memcpy_site_tfa B ->
eagree E3 -> st_ok tfibsegs E3 S_CP (restrict (w_H W) ms) ->
bv_unsigned (ew E3 A_BUF) = buf -> bv_unsigned (ew E3 A_LEN) = len -> bv_unsigned (ew E3 A_N) = n ->
AR tfibsegs B ly S W (ms_mem ms) md -> top_ok usp ly ->
blocks S = [(pb, cap)] -> sptr_addr B ly pb = buf -> 0 <= len -> 1 <= n <= 65536 -> len + n <= cap -> cap <= 2 ^ 26 ->
blk (w_H W) (ms_mem ms) buf len data -> Z.of_nat (length bs) = n ->
(forall i, 0 <= i < n -> ms_mem ms (Z_to_bv 64 (RS_LO + i)) = nth_error bs (Z.to_nat i)) ->
(forall j, (j < length bs)%nat -> nth_error bs j = nth_error data (Z.to_nat len + j)%nat) ->
SRr tfibsegs W (mkCfg ms md)
(fun W' c' => W' = W /\ exists regs4 mem4 md4,
c' = mkCfg (mkst regs4 (Z_to_bv 64 RA_CP) mem4 (seg_rom tfibsegs)) md4
/\ st_ok tfibsegs (havoc E3 K_CP (map (getr regs4) CLOB)) S_CPp (restrict (w_H W) (mkst regs4 (Z_to_bv 64 RA_CP) mem4 (seg_rom tfibsegs)))
/\ AR tfibsegs B ly S W mem4 md4 /\ same_but_materialized md md4
/\ blk (w_H W) mem4 buf (len + n) data
/\ (forall a, 0 <= a < 2 ^ 64 -> ~ (buf + len <= a < buf + len + n) -> ~ (usp - 128 - ESTACK <= a < usp - 128) -> aview tfibsegs (w_H W) mem4 a = aview tfibsegs (w_H W) (ms_mem ms) a)
/\ (forall a, apresent (w_H W) (ms_mem ms) a -> apresent (w_H W) mem4 a)).
Proof.
intros E3 W ms md ly S pb n buf len cap data bs MCPY HE HS E46 E58 E78 HAR HTOP Hbl Hpb Hlen0 Hn Hle Hcap HBLK Hbs Hrs Hslice.
pose proof Hsp as (Ulo & Uhi & U16). pose proof (u64_range sp) as Usp. pose proof (eagree_0 E3 HE) as E0'. pose proof (eagree_6 E3 HE) as E6'.
assert (Hin : In (buf, cap) (ablocks B ly S)) by (unfold ablocks; rewrite Hbl, <- Hpb; left; reflexivity).
pose proof (al_blocks _ _ ARL ly S W (ms_mem ms) md buf cap HAR Hin) as (Hbufm & Hb4096 & Hbce & Happ & Hbytes & _).
assert (Hcapr : cap <= req_size cap) by (unfold req_size; destruct (Z.eqb_spec cap 0); lia).
pose proof (YM05.ceil_le_top _ (top_ok_ceil _ _ HTOP)) as CLE. unfold stack_max_size in CLE.
pose proof (proj1 (@YG0f.ASAN_CEIL_range _)) as CR. unfold ASAN_CEIL in CR.
pose proof (st_ok_restrict_mkst tfibsegs (w_H W) E3 S_CP ms HS eq_refl) as Hshape.
set (regs := ms_regs ms) in *. set (mem := ms_mem ms) in *.
pose proof S_CP_facts as (_ & Fra & Fa0 & Fa1 & Fa2 & _ & Fsp).
assert (R1 : getr regs 1%bv = w64 RA_CP) by (rewrite (st_ok_restrict_reg tfibsegs (w_H W) E3 S_CP ms 1%bv HS), Fra; reflexivity).
assert (R3 : getr regs 3%bv = w64 TFIB_GP) by (rewrite (st_ok_restrict_reg tfibsegs (w_H W) E3 S_CP ms 3%bv HS); reflexivity).
assert (R4 : getr regs 4%bv = w64 TFIB_TP) by (rewrite (st_ok_restrict_reg tfibsegs (w_H W) E3 S_CP ms 4%bv HS); reflexivity).
assert (R2 : getr regs 2%bv = Z_to_bv 64 (usp + -128)).
{ rewrite (st_ok_restrict_reg tfibsegs (w_H W) E3 S_CP ms 2%bv HS), Fsp. cbn [sv_denot]. rewrite E0'. reflexivity. }
assert (R10 : getr regs 10%bv = w64 (buf + len)).
{ pose proof E46 as E46'. pose proof E58 as E58'. unfold A_BUF in E46'. unfold A_LEN in E58'.
rewrite (st_ok_restrict_reg tfibsegs (w_H W) E3 S_CP ms 10%bv HS), Fa0. rewrite (denot_lit_U E3). unfold w64. f_equal.
rewrite U_SAlu. cbn [zalu_raw]. rewrite !U_SOff. rewrite !Z.add_0_r. first [rewrite E46 | rewrite E46']. first [rewrite E58 | rewrite E58'].
rewrite (zcanon_id buf), (zcanon_id len) by (unfold M64; lia).
apply zcanon_id. unfold M64; lia. }
assert (R11 : getr regs 11%bv = w64 RS_LO) by (rewrite (st_ok_restrict_reg tfibsegs (w_H W) E3 S_CP ms 11%bv HS), Fa1; reflexivity).
assert (R12 : getr regs 12%bv = w64 n).
{ rewrite (st_ok_restrict_reg tfibsegs (w_H W) E3 S_CP ms 12%bv HS), Fa2. cbn [sv_denot]. pose proof E78 as E78'. unfold A_N in E78'.
rewrite Z.add_0_r. first [rewrite E78 | rewrite E78']. reflexivity. }
assert (Hsp' : spZ regs = usp - 128) by (unfold spZ; rewrite R2; rewrite u64_lit by (unfold sp_window_lo in Ulo; lia); lia).
pose proof (st_ok_mem_ok tfibsegs E3 S_CP _ HS) as HM. cbn [restrict ms_mem] in HM. fold mem in HM.
assert (Hwin : forall a, usp - 65536 <= a < usp - 128 -> apresent (w_H W) mem a).
{ intros a Ha. eapply (win_present sp Hsp E3 (w_H W) mem (ss_mem S_CP)); [exact HM | left; reflexivity | exact E0' | lia | lia | cbn; lia]. }
assert (NIMG : forall a, buf <= a < buf + req_size cap -> ~ in_img tfibsegs a).
{ intros a Ha. exact (proj2 (al_client_img _ _ ARL ly S W mem md a HAR (or_introl (ex_intro _ buf (ex_intro _ cap (conj Hin Ha)))))). }
rewrite Hshape. change (Z_to_bv 64 (ss_pc S_CP)) with (w64 A_icpt_memcpy). fold regs mem.
change (mkCfg (mkst regs (w64 A_icpt_memcpy) mem (seg_rom tfibsegs)) md) with (cfg_at tfibsegs A_icpt_memcpy regs mem md).
change A_icpt_memcpy with (pc_wrap_memcpy Tfib_code). rewrite <- (ts_code B HB).
eapply SRr_mono.
{ apply (MCPY ly S W regs mem md (buf + len) RS_LO n).
- split; [exact HAR|]. split; [unfold top_ok in *; tauto|]. split; [rewrite R1; unfold YK0s.ret_ok; apply bv_eq; vm_compute; reflexivity|].
split; [rewrite Hsp'; replace (usp - 128) with (usp + (-8) * 16) by lia; rewrite Z.mod_add by lia; exact U16|].
split; [rewrite Hsp'; unfold sp_window_lo in *; lia|]. split; [rewrite Hsp'; unfold top_ok in HTOP; lia|].
split; [rewrite Hsp'; intros a Ha; apply Hwin; unfold ESTACK in Ha; lia|].
split; [rewrite (ts_gp B HB); exact R3 | rewrite (ts_tp B HB); exact R4].
- exact R10.
- exact R11.
- exact R12.
- lia.
- lia.
- lia.
-   intros a Ha. split; [| split].
+ apply (apresent_writable tfibsegs). exact (proj1 (Hbytes a ltac:(lia))).
+ exact (proj2 (Hbytes a ltac:(lia))).
+ rewrite Hsp'. unfold ESTACK. lia.
-   unfold amem_range. destruct Happ as [_ [Hlow | [Hh1 Hh2]]].
+ left. unfold kLowShadowBeg, kLowMemEnd in *. lia.
+ right. unfold kHighMemEnd in *. lia.
- apply (range_addressable_of_block' ly S W mem md buf cap); [exact HAR | exact Hin | lia | lia].
- intros _. apply (shadow_hull_vis_of_block' ly S W mem md buf cap); [exact HAR | exact Hin | lia | lia | lia].
- unfold RS_LO; lia.
- unfold RS_LO; lia.
-
intros a Ha. split.
+ unfold aview, mbyte, mrestrict. rewrite (seg_win_visible W RS_LO 65536 a (proj2 rs_win_check)) by (unfold RS_LO in *; lia).
specialize (Hrs (a - RS_LO) ltac:(lia)). replace (RS_LO + (a - RS_LO)) with a in Hrs by lia. fold mem in Hrs. rewrite Hrs.
destruct (nth_error bs (Z.to_nat (a - RS_LO))) eqn:En; [cbn; discriminate | apply nth_error_None in En; lia].
+ rewrite Hsp'. unfold RS_LO, ESTACK, sp_window_lo in *. lia.
-   destruct (Z.le_gt_cases (buf + len + n) RS_LO) as [|Hgt]; [left; exact H|]. right.
destruct (Z.le_gt_cases (RS_LO + n) (buf + len)) as [|Hgt2]; [lia|]. exfalso.
destruct (Z.le_gt_cases RS_LO (buf + len)) as [Hc|Hc].
+ apply (NIMG (buf + len) ltac:(lia)). apply rs_in_img. unfold RS_LO, RS_HI in *. lia.
+ apply (NIMG RS_LO ltac:(lia)). apply rs_in_img. unfold RS_LO, RS_HI. lia.
- left. unfold RS_LO, kLowMemEnd. lia.
- apply (rs_range_addressable ly S W mem md n HAR); [lia | unfold RS_LO, RS_HI; lia].
- intros _. apply (rs_shadow_hull_vis ly S W mem md n HAR); [lia | unfold RS_LO, RS_HI; lia]. }
cbv beta. intros W' c' _ (-> & regs4 & mem4 & md4 & -> & HAR4 & HP & Hs & Ha0 & Hcp & Hfr & Hpres).
unfold raZ. rewrite R1. unfold w64. rewrite u64_lit by (unfold RA_CP; lia).
split; [reflexivity|]. exists regs4, mem4, md4. split; [reflexivity|].
rewrite Hshape, restrict_mkst_fx in HS. fold regs mem in HS.
assert (HST : st_ok tfibsegs (havoc E3 K_CP (map (getr regs4) CLOB)) S_CPp (mkst regs4 (Z_to_bv 64 RA_CP) (mrestrict (w_H W) mem4) (seg_rom tfibsegs))).
{ rewrite <- (proj1 S_eq_certs). unfold drv_after. change (junk_upd K_CP CLOB) with ([] ++ junk_upd K_CP CLOB).
apply (st_ok_splice_havoc tfibsegs K_CP E3 S_CP regs regs4 (w64 A_icpt_memcpy) RA_CP (mrestrict (w_H W) mem) (mrestrict (w_H W) mem4)
(WIN (-128) :: rs_CP) [] CLOB HS).
- exact (proj1 cp_checks).
- vm_compute. reflexivity.
- vm_compute. reflexivity.
- reflexivity.
- exact (proj1 (proj2 (proj2 (proj2 cp_checks)))).
- cbn [map app]. apply regs_preserved_frame. apply aregs_regs_preserved. exact HP.
- constructor.
-
assert (SCR : forall a, 0 <= a < 2 ^ 64 -> ~ (buf + len <= a < buf + len + n) -> ~ (usp - 128 - ESTACK <= a < usp - 128) ->
mbyte tfibsegs (mrestrict (w_H W) mem4) a = mbyte tfibsegs (mrestrict (w_H W) mem) a).
{ intros a H0 H1 H2. apply (mbyte_of_aview tfibsegs). apply Hfr; [exact H0 | exact H1 | rewrite Hsp'; exact H2]. }
destruct HM as (Hwf & Hok & Hpd).
split; [exact (proj1 (proj2 cp_checks))|]. split.
+ pose proof (Forall_inv Hok) as Hr0. pose proof (Forall_inv_tail Hok) as Hrs0.
constructor.
*
split; [cbn [base_val r_base r_lo WIN]; rewrite E0'; unfold sp_window_lo in Ulo; lia|].
split; [cbn [base_val r_base r_hi WIN]; rewrite E0'; lia|]. split; [| constructor].
cbn [r_wlo r_whi r_base base_val WIN]. rewrite E0'. intros o Ho. apply (apresent_writable tfibsegs). apply Hpres. apply Hwin. lia.
* assert (Hsub : submem rs_CP (ss_mem S_CP)).
{ rewrite (proj2 (proj2 (proj2 (proj2 (proj2 cp_checks))))). change (ss_mem S_CP) with (hd R_errno (ss_mem S_CP) :: tl (ss_mem S_CP)). apply submem_drop. apply submem_filter. }
assert (HMt : mem_ok tfibsegs E3 (mrestrict (w_H W) mem) rs_CP).
{ apply (mem_ok_sub tfibsegs E3 _ _ rs_CP Hsub). 2:{ split; [exact Hwf|]. split; [exact Hok | exact Hpd]. }
pose proof (proj1 (proj2 cp_checks)) as W2. cbn in W2. apply andb_prop in W2. tauto. }
assert (HK : Forall (region_kept tfibsegs E3 (mrestrict (w_H W) mem) (mrestrict (w_H W) mem4)) rs_CP).
{ apply Forall_forall. intros r Hr.
pose proof (proj1 (forallb_forall _ _) (proj1 (proj2 (proj2 (proj2 (proj2 cp_checks))))) r Hr) as Hc. unfold drv_keep_ok in Hc.
pose proof (proj1 (Forall_forall _ _) (proj1 (proj2 HMt)) r Hr) as (B1 & B2 & _).
assert (OFF : forall a, base_val E3 (r_base r) + r_lo r <= a < base_val E3 (r_base r) + r_hi r ->
~ (buf + len <= a < buf + len + n) /\ ~ (usp - 128 - ESTACK <= a < usp - 128)).
{ intros a Ha. destruct (r_base r) as [[|[|[|[|[|[|[|k]]]]]]]|]; try discriminate Hc; cbn [base_val] in Ha, B1, B2.
- apply andb_prop in Hc as [Hc _]. apply Z.leb_le in Hc. rewrite E0' in Ha. unfold ESTACK, sp_window_lo in *. lia.
- apply andb_prop in Hc as [Hc _]. apply Z.leb_le in Hc. pose proof (u64_range (ew E3 6)). unfold ESTACK, sp_window_lo in *. lia.
- apply andb_prop in Hc as [Hc _]. apply andb_prop in Hc as [Hc _]. apply andb_prop in Hc as [Hc1 Hc2].
apply Z.leb_le in Hc1. apply Z.leb_le in Hc2. split; [| unfold ESTACK, sp_window_lo in *; lia].
intros Hab. apply (NIMG a ltac:(lia)). apply in_img_hull. lia. }
split; intros a Ha; [apply SCR; [lia | apply OFF; exact Ha | apply OFF; exact Ha]|].
intros Hw. exact (wview_grows tfibsegs _ _ _ (mem_grows_of_apresent (w_H W) mem mem4 Hpres) Hw). }
exact (proj1 (proj2 (mem_ok_kept tfibsegs E3 _ (mrestrict (w_H W) mem4) rs_CP HMt ltac:(pose proof (proj1 (proj2 cp_checks)) as W2; cbn in W2; apply andb_prop in W2; tauto) HK))).
+
assert (Hsub : submem rs_CP (ss_mem S_CP)).
{ rewrite (proj2 (proj2 (proj2 (proj2 (proj2 cp_checks))))). change (ss_mem S_CP) with (hd R_errno (ss_mem S_CP) :: tl (ss_mem S_CP)). apply submem_drop. apply submem_filter. }
assert (HMt : mem_ok tfibsegs E3 (mrestrict (w_H W) mem) rs_CP).
{ apply (mem_ok_sub tfibsegs E3 _ _ rs_CP Hsub). 2:{ split; [exact Hwf|]. split; [exact Hok | exact Hpd]. }
pose proof (proj1 (proj2 cp_checks)) as W2. cbn in W2. apply andb_prop in W2. tauto. }
split; [| exact (proj2 (proj2 HMt))].
pose proof (proj1 (proj2 (proj2 (proj2 (proj2 cp_checks))))) as Hchk. clear - Hchk E0' E6' Ulo. unfold sp_window_lo in Ulo.
induction rs_CP as [|r rs IH]; cbn; [exact I|]. cbn in Hchk. apply andb_prop in Hchk as [Hc Hchk].
split; [|exact (IH Hchk)]. unfold extent_disjoint. cbn [r_base r_lo r_hi WIN base_val]. rewrite E0'.
unfold drv_keep_ok in Hc. destruct (r_base r) as [[|[|[|[|[|[|[|k]]]]]]]|]; try discriminate Hc; cbn [base_val].
* apply andb_prop in Hc as [Hc _]. apply Z.leb_le in Hc. rewrite E0'. left. lia.
* apply andb_prop in Hc as [Hc _]. apply Z.leb_le in Hc. left. pose proof (u64_range (ew E3 6)). lia.
* apply andb_prop in Hc as [Hc _]. apply andb_prop in Hc as [Hc _]. apply andb_prop in Hc as [_ Hc]. apply Z.leb_le in Hc. right. lia. }
rewrite <- restrict_mkst_fx in HST. split; [exact HST|]. split; [exact HAR4|]. split; [exact Hs|].
split; [| split; [intros a H0 H1 H2; apply Hfr; [exact H0 | exact H1 | rewrite Hsp'; exact H2] | exact Hpres]].
intros i Hi. destruct (Z.lt_ge_cases i len) as [Hil|Hil].
- rewrite <- (HBLK i ltac:(lia)). apply (restrict_of_aview (w_H W) mem mem4 (buf + i)); [lia | apply NIMG; lia |].
apply Hfr; [lia | lia | rewrite Hsp'; unfold ESTACK; lia].
- pose proof (Hcp (i - len) ltac:(lia)) as X. replace (buf + len + (i - len)) with (buf + i) in X by lia.
pose proof (Hrs (i - len) ltac:(lia)) as Y. rewrite (Hslice (Z.to_nat (i - len)) ltac:(lia)) in Y.
replace (Z.to_nat len + Z.to_nat (i - len))%nat with (Z.to_nat i) in Y by lia.
destruct (nth_error data (Z.to_nat i)) as [b|] eqn:En.
+ apply (restrict_some_of_aview (w_H W) mem4 (buf + i) b); [lia | apply NIMG; lia |]. rewrite X.
unfold aview, mbyte, mrestrict. rewrite (seg_win_visible W RS_LO 65536 (RS_LO + (i - len)) (proj2 rs_win_check)) by (unfold RS_LO in *; lia).
fold mem. rewrite Y. reflexivity.
+ exfalso. pose proof (Hslice (Z.to_nat (i - len)) ltac:(lia)) as Z1.
replace (Z.to_nat len + Z.to_nat (i - len))%nat with (Z.to_nat i) in Z1 by lia. rewrite En in Z1.
apply nth_error_None in Z1. lia.
Qed.
End f.
End Rd.
End e.
