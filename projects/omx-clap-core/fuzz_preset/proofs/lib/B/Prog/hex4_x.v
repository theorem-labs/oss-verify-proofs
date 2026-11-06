(* Theorem Labs, 2026-10: hex4's walk in fuzz_preset's asan-ubsan image (B, img_sigma AS_hex4, 260 bytes), in the cgif donor's program-walk form over YCbqG's journal layer; the table is lib/B/PAImg_leaves.v's hex4_tbl. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn YP0b YP0a.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YN3v YI04 YG0s YP07.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq YCbqG.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YM05 YI16.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YP0d YP0c YPsym YC4aP YC1fP YImgTop.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YI00.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require PjGrammar.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Prog Require Import hex4_xs.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B Require Import Img0 Listing_leaves PAImg_leaves.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.
Definition HEX4_B : Z := img_sigma AS_hex4.
Definition GOT_SHADOW_B : Z := hex4_val (A_OBJ 0).
Definition SHADOW_CELL_B : Z := hex4_val (A_OBJ 12).
Section pcs. Context {rc : YM05.RunCeil}.
Remark hex4_B_pc : HEX4_B = pa_val (PAImg := PI_hex4) A_TEXT. Proof. vm_compute. reflexivity. Qed.
Remark hex4_B_got : GOT_SHADOW_B = pa_val (PAImg := PI_hex4) (A_OBJ 0). Proof. vm_compute. reflexivity. Qed.
Remark hex4_B_cell : SHADOW_CELL_B = pa_val (PAImg := PI_hex4) (A_OBJ 12). Proof. vm_compute. reflexivity. Qed.
End pcs.
Definition XBx : sv := SOff 32 0.
Definition XSPAN : Z * Z := (SHADOW_OFF, SHADOW_OFF + 2 ^ 44 - 1).
Definition SRCx (hi : Z) : afact := mkAF 4096 hi 0.
Definition OUTx : afact := mkAF (2 ^ 46) (2 ^ 47 - 4) 2.
Definition SPfact : afact := mkAF (2 ^ 46) (2 ^ 47) 4.
Definition SBfact : afact := mkAF SHADOW_OFF SHADOW_OFF 0.
Definition gotR : YP09.region :=
YP09.mkRegion None GOT_SHADOW_B (GOT_SHADOW_B + 8) 0 0 [YP09.mkChunk GOT_SHADOW_B (CVal 8 (SLit SHADOW_CELL_B))].
Definition cellR : YP09.region :=
YP09.mkRegion None SHADOW_CELL_B (SHADOW_CELL_B + 8) 0 0 [YP09.mkChunk SHADOW_CELL_B (CVal 8 (SOff 32 0))].
Definition stkE : YP09.region := YP09.mkRegion (Some 2%nat) (-16) 0 (-16) 0 [].
Definition SHe : list shent := [mkSHE 10 0 4; mkSHE 11 0 4].
Definition ss_e : sstate :=
mkSS HEX4_B sr_atoms [stkE; gotR; cellR] None
(mkFacts [(2%nat, SPfact); (10%nat, SRCx (2 ^ 47 - 4)); (11%nat, OUTx); (32%nat, SBfact)] [] []).
Definition Ke : nat := run_K 33 XBx SHe ss_e.
Lemma ss_e_static : sh_static_ok Ke XBx XSPAN SHe (ss_facts ss_e) (ss_mem ss_e) = true.
Proof. vm_compute. reflexivity. Qed.
Definition XBxL : sv := SOff 14 0.
Definition stkL : YP09.region := YP09.mkRegion (Some 2%nat) 0 16 0 0 [YP09.mkChunk 8 (CVal 8 (SOff 1 0))].
Definition curR : YP09.region := YP09.mkRegion (Some 32%nat) 0 1 0 0 [YP09.mkChunk 0 (CVal 1 (SOff 33 0))].
Definition outR : YP09.region := YP09.mkRegion (Some 11%nat) 0 4 0 4 [].
Definition SHl : list shent := [mkSHE 32 0 1; mkSHE 11 0 4].
Definition loop_regs : list sv :=
sr_set (sr_set (sr_set (sr_set (sr_set (sr_set (sr_set (sr_set sr_atoms
  12%bv (SOff 32 0)) 7%bv (SOff 32 0)) 15%bv (SOff 35 0)) 16%bv (SLit 1))
  17%bv (SLit 10)) 5%bv (SLit 6)) 6%bv (SLit 5)) 13%bv (SOff 34 0).
Definition ss_l : sstate :=
mkSS (HEX4_B + 0x34) loop_regs [stkL; curR] None
(mkFacts [(2%nat, SPfact); (10%nat, SRCx (2 ^ 47 - 4)); (11%nat, OUTx); (14%nat, SBfact); (32%nat, SRCx (2 ^ 47 - 1));
          (33%nat, mkAF 0 255 0); (34%nat, mkAF 0 65535 0); (35%nat, mkAF 1 4 0)] [] []).
Definition Kl : nat := run_K 36 XBxL SHl ss_l.
Lemma ss_l_static : sh_static_ok Kl XBxL XSPAN SHl (ss_facts ss_l) (ss_mem ss_l) = true.
Proof. vm_compute. reflexivity. Qed.
Definition SHf : list shent := [mkSHE 11 0 4].
Definition fin_regs : list sv := sr_set sr_atoms 13%bv (SOff 32 0).
Definition ss_f : sstate :=
mkSS (HEX4_B + 0xb8) fin_regs [stkL; outR] None
(mkFacts [(2%nat, SPfact); (11%nat, OUTx); (14%nat, SBfact); (32%nat, mkAF 0 65535 0)] [] []).
Definition Kf : nat := run_K 36 XBxL SHf ss_f.
Lemma ss_f_static : sh_static_ok Kf XBxL XSPAN SHf (ss_facts ss_f) (ss_mem ss_f) = true.
Proof. vm_compute. reflexivity. Qed.
Definition ss_q : sstate :=
mkSS (HEX4_B + 0xdc) sr_atoms [stkL] None (mkFacts [(2%nat, SPfact)] [] []).
Lemma ss_q_static : sh_static_ok (run_K 36 XBxL [] ss_q) XBxL XSPAN [] (ss_facts ss_q) (ss_mem ss_q) = true.
Proof. vm_compute. reflexivity. Qed.
Lemma lor_low4 : forall x y, 0 <= x < 16 -> 0 <= y -> Z.lor x (y * 16) = 16 * y + x.
Proof.
intros x y Hx Hy. replace (y * 16) with (Z.shiftl y 4) by (rewrite Z.shiftl_mul_pow2 by lia; cbn; lia).
assert (H0 : Z.land x (Z.shiftl y 4) = 0).
{ apply Z.bits_inj'. intros i Hi. rewrite Z.land_spec, Z.bits_0.
destruct (Z.lt_ge_cases i 4).
- rewrite Z.shiftl_spec_low by lia. apply andb_false_r.
- rewrite <- (Z.mod_small x (2 ^ 4)) by (change (2 ^ 4) with 16; lia).
rewrite Z.mod_pow2_bits_high by lia. reflexivity. }
rewrite <- (Z.lxor_lor _ _ H0), <- (Z.add_nocarry_lxor _ _ H0), Z.shiftl_mul_pow2 by lia.
change (2 ^ 4) with 16. lia.
Qed.
Lemma acc_or : forall (E : env) (n1 n2 : nat) (cc vv delta : Z),
bv_unsigned (ew E n1) = cc -> bv_unsigned (ew E n2) = vv ->
0 <= vv < 4096 -> 0 <= cc + delta < 16 ->
sv_denot E (SAlu ALU_OR (SOff n1 delta) (SAlu ALU_SLL (SOff n2 0) (SLit 4))) = w64 (16 * vv + (cc + delta)).
Proof.
intros E n1 n2 cc vv delta H1 H2 Hv Hd.
rewrite denot_lit_U. unfold w64. f_equal.
rewrite U_SAlu. cbn [zalu_raw].
rewrite (U_SOff E n1 delta), H1, (zcanon_id (cc + delta)) by (unfold M64; lia).
rewrite U_SAlu. cbn [zalu_raw].
rewrite (U_SOff E n2 0), H2, Z.add_0_r, (zcanon_id vv) by (unfold M64; lia).
rewrite U_SLit, (zcanon_id 4) by (unfold M64; lia).
change (Z.land 4 63) with 4. rewrite Z.shiftl_mul_pow2 by lia. change (2 ^ 4) with 16.
rewrite (zcanon_id (vv * 16)) by (unfold M64; lia).
rewrite lor_low4 by lia. apply zcanon_id. unfold M64. lia.
Qed.
Ltac hexval_solve :=
unfold PjGrammar.hexval;
repeat match goal with |- context [Z.leb ?a ?b] => destruct (Z.leb_spec a b) end; cbn [andb];
first [ reflexivity | f_equal; lia | exfalso; lia ].
Lemma no_wrange_lc : forall E a, ~ in_wrange E [stkL; curR] a.
Proof.
intros E a (r & Hin & Hr). cbn [In] in Hin. destruct Hin as [<-|[<-|[]]];
unfold stkL, curR in Hr; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi base_val] in Hr; lia.
Qed.
Lemma lt_mod_iff : forall c delta n, 0 <= c < 256 -> -256 <= delta <= 0 -> 0 <= n < 256 ->
((c + delta) mod 2 ^ 64 < n mod 2 ^ 64 <-> 0 <= c + delta < n).
Proof.
intros c delta n Hc Hd Hn. rewrite (Z.mod_small n) by lia.
destruct (Z.le_gt_cases 0 (c + delta)) as [Hge|Hlt].
- rewrite Z.mod_small by lia. split; lia.
- rewrite <- (Z.mod_add (c + delta) 1 (2 ^ 64)) by lia. rewrite Z.mod_small by lia. split; lia.
Qed.
Lemma lt_mod_iff2 : forall c delta n, 0 <= c < 256 -> -256 <= delta <= 0 -> 0 <= n < 256 ->
(n mod 2 ^ 64 < (c + delta) mod 2 ^ 64 <-> (c + delta < 0 \/ n < c + delta)).
Proof.
intros c delta n Hc Hd Hn. rewrite (Z.mod_small n) by lia.
destruct (Z.le_gt_cases 0 (c + delta)) as [Hge|Hlt].
- rewrite Z.mod_small by lia. split; lia.
- rewrite <- (Z.mod_add (c + delta) 1 (2 ^ 64)) by lia. rewrite Z.mod_small by lia. split; lia.
Qed.
Definition hex4_src_ok (p : Z) : Prop := 4096 <= p /\ (p + 4 < 0x7fff8000 \/ (0x10007fff8000 <= p /\ p + 4 < 2 ^ 47)).
Definition hex4_out_ok (o : Z) : Prop := 2 ^ 46 <= o /\ o + 4 <= 2 ^ 47.
Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable SK : YI16.sink_head.
Variable B : asyms.
Variable PST : list (Z * Z).
Variable ARx : alayout -> astate -> list Z -> world rsegs -> (word -> option byte) -> Model -> Prop.
Context {HL : Z}.
Hypothesis LAWS : AR_laws_x rsegs B ARx HL.
Hypothesis TL : PALibCore (PI := PI_hex4) B.
Let HGOT : as_got_shadow B = GOT_SHADOW_B := eq_trans (palc_got_shadow B TL) (eq_sym hex4_B_got).
Let HCELL : as_shadow_cell B = SHADOW_CELL_B := eq_trans (palc_cell B TL) (eq_sym hex4_B_cell).
Definition HEX4_KEPT : list (bv 5) := [1; 3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%bv.
Let RUN := @SRr_run_tok_AJx fx rc SK rsegs B PST ARx _ LAWS img_segs_low hex4_tbl hex4_tbl_ok img_wx.
Let RUNTO := @SRr_run_to_tok_AJx fx rc SK rsegs B PST ARx _ LAWS img_segs_low hex4_tbl hex4_tbl_ok img_wx.
Let RET := @SRr_ret_at rsegs fx hex4_tbl hex4_tbl_ok img_wx.
Lemma st_ok_region_nth : forall E ss ms i r,
st_ok rsegs E ss ms -> nth_error (ss_mem ss) i = Some r -> region_ok rsegs E (ms_mem ms) r.
Proof.
intros E ss ms i r HS Hi. destruct (st_ok_mem_ok rsegs E ss ms HS) as (_ & Hrs & _).
exact (proj1 (Forall_forall _ _) Hrs r (nth_error_In _ _ Hi)).
Qed.
Lemma frame_aview : forall E rs (m m' : word -> option byte) (H : word -> bool) a,
frame_of E rs (mrestrict H m) (mrestrict H m') -> 0 <= a < 2 ^ 64 -> ~ in_wrange E rs a ->
aview rsegs H m' a = aview rsegs H m a.
Proof.
intros E rs m m' H a HF Ha Hw. unfold aview, mbyte.
rewrite (HF (Z_to_bv 64 a)) by (rewrite unsigned_lit_small by lia; exact Hw). reflexivity.
Qed.
Definition keeps (W : world rsegs) (m m' : word -> option byte) : Prop :=
forall x, 0 <= x < 2 ^ 64 -> aview rsegs (w_H W) m' x = aview rsegs (w_H W) m x.
Lemma keeps_val_mem : forall W m m' a (n : nat) val,
keeps W m m' -> 0 <= a -> a + Z.of_nat n <= 2 ^ 64 ->
val_mem rsegs (mrestrict (w_H W) m) a n val -> val_mem rsegs (mrestrict (w_H W) m') a n val.
Proof.
intros W m m' a n val HK Ha Han HV j Hj.
assert (Hx : 0 <= a + Z.of_nat j < 2 ^ 64) by lia.
rewrite (mbyte_of_aview rsegs (w_H W) (w_H W) m m' (a + Z.of_nat j) (HK _ Hx)). exact (HV j Hj).
Qed.
Lemma keeps_garr8 : forall W m m' a (l : list Z),
keeps W m m' -> 0 <= a -> a + Z.of_nat (length l) <= 2 ^ 64 ->
garr8 rsegs (mrestrict (w_H W) m) a l -> garr8 rsegs (mrestrict (w_H W) m') a l.
Proof.
intros W m m' a l HK Ha Hal HG j Hj. destruct (HG j Hj) as [HV Hr]. split; [|exact Hr].
assert (H1 : 0 <= a + Z.of_nat j) by lia.
assert (H2 : a + Z.of_nat j + Z.of_nat 1 <= 2 ^ 64) by (cbn; lia).
exact (keeps_val_mem W m m' (a + Z.of_nat j) 1 (nth j l 0) HK H1 H2 HV).
Qed.
Lemma keeps_ra : forall W m m' a n,
keeps W m m' -> 0 <= a -> a + n <= 2 ^ 64 ->
range_addressable (aview rsegs (w_H W) m) SHADOW_OFF a n ->
range_addressable (aview rsegs (w_H W) m') SHADOW_OFF a n.
Proof.
intros W m m' a n HK Ha Han HR x Hx. destruct (HR x Hx) as (s & Hs & Hok).
exists s. split; [|exact Hok]. rewrite HK; [exact Hs|]. unfold shadow_of_addr, SHADOW_OFF in *. lia.
Qed.
Lemma keeps_trans : forall W m1 m2 m3, keeps W m1 m2 -> keeps W m2 m3 -> keeps W m1 m3.
Proof. intros W m1 m2 m3 H1 H2 x Hx. rewrite (H2 x Hx), (H1 x Hx). reflexivity. Qed.
Lemma keeps_refl : forall W m, keeps W m m.
Proof. intros W m x Hx. reflexivity. Qed.
Lemma keeps_of_frame : forall W E (rs : smem) m m',
(forall a, ~ in_wrange E rs a) -> frame_of E rs (mrestrict (w_H W) m) (mrestrict (w_H W) m') -> keeps W m m'.
Proof. intros W E rs m m' Hn HF x Hx. exact (frame_aview E rs m m' (w_H W) x HF Hx (Hn x)). Qed.
Lemma awr_ok_lc : forall E STK sp0 FP bl0 blc ly own, awr_ok E [stkL; curR] STK sp0 FP bl0 blc ly own.
Proof. intros E STK sp0 FP bl0 blc ly own a Ha. exfalso. exact (no_wrange_lc E a Ha). Qed.
Lemma hexval_range : forall c d, PjGrammar.hexval c = Some d -> 0 <= d < 16.
Proof.
intros c d. unfold PjGrammar.hexval.
repeat match goal with |- context [Z.leb ?a ?b] => destruct (Z.leb_spec a b) end; cbn [andb];
intro Hs; try discriminate Hs; injection Hs as E; subst d; lia.
Qed.
Lemma garr8_hd : forall (W : world rsegs) m a c l, garr8 rsegs (mrestrict (w_H W) m) a (c :: l) ->
val_mem rsegs (mrestrict (w_H W) m) a 1 c /\ 0 <= c < 256.
Proof.
intros W m a c l HG. destruct (HG 0%nat ltac:(cbn; lia)) as [HV Hr]. cbn [nth] in HV, Hr.
rewrite Z.add_0_r in HV. split; [exact HV | exact Hr].
Qed.
Lemma garr8_tl : forall (W : world rsegs) m a c l, garr8 rsegs (mrestrict (w_H W) m) a (c :: l) ->
garr8 rsegs (mrestrict (w_H W) m) (a + 1) l.
Proof.
intros W m a c l HG j Hj. destruct (HG (S j) ltac:(cbn; lia)) as [HV Hr]. cbn [nth] in HV, Hr.
replace (a + 1 + Z.of_nat j) with (a + Z.of_nat (S j)) by lia. split; [exact HV | exact Hr].
Qed.
Definition keeps_out (W : world rsegs) (lo hi : Z) (m m' : word -> option byte) : Prop :=
forall x, 0 <= x < 2 ^ 64 -> ~ (lo <= x < hi) -> aview rsegs (w_H W) m' x = aview rsegs (w_H W) m x.
Lemma out_val_mem : forall (W : world rsegs) lo hi m m' a (n : nat) val,
keeps_out W lo hi m m' -> 0 <= a -> a + Z.of_nat n <= 2 ^ 64 -> (a + Z.of_nat n <= lo \/ hi <= a) ->
val_mem rsegs (mrestrict (w_H W) m) a n val -> val_mem rsegs (mrestrict (w_H W) m') a n val.
Proof.
intros W lo hi m m' a n val HK Ha Han Hd HV j Hj.
assert (Hx : 0 <= a + Z.of_nat j < 2 ^ 64) by lia.
assert (Hnx : ~ (lo <= a + Z.of_nat j < hi)) by lia.
rewrite (mbyte_of_aview rsegs (w_H W) (w_H W) m m' (a + Z.of_nat j) (HK _ Hx Hnx)). exact (HV j Hj).
Qed.
Lemma out_garr8 : forall W lo hi m m' a (l : list Z),
keeps_out W lo hi m m' -> 0 <= a -> a + Z.of_nat (length l) <= 2 ^ 64 ->
(a + Z.of_nat (length l) <= lo \/ hi <= a) ->
garr8 rsegs (mrestrict (w_H W) m) a l -> garr8 rsegs (mrestrict (w_H W) m') a l.
Proof.
intros W lo hi m m' a l HK Ha Hal Hd HG j Hj. destruct (HG j Hj) as [HV Hr]. split; [|exact Hr].
assert (H1 : 0 <= a + Z.of_nat j) by lia.
assert (H2 : a + Z.of_nat j + Z.of_nat 1 <= 2 ^ 64) by (cbn; lia).
assert (H3 : a + Z.of_nat j + Z.of_nat 1 <= lo \/ hi <= a + Z.of_nat j) by (cbn; lia).
exact (out_val_mem W lo hi m m' (a + Z.of_nat j) 1 (nth j l 0) HK H1 H2 H3 HV).
Qed.
Lemma out_ra : forall W lo hi m m' a n,
keeps_out W lo hi m m' -> 0 <= a -> a + n <= 2 ^ 47 -> SHADOW_OFF + 2 ^ 44 <= lo ->
range_addressable (aview rsegs (w_H W) m) SHADOW_OFF a n ->
range_addressable (aview rsegs (w_H W) m') SHADOW_OFF a n.
Proof.
intros W lo hi m m' a n HK Ha Han Hlo HR x Hx. destruct (HR x Hx) as (s & Hs & Hok).
exists s. split; [|exact Hok]. unfold shadow_of_addr in *.
rewrite HK; [exact Hs | unfold SHADOW_OFF in *; lia | unfold SHADOW_OFF in *; lia].
Qed.
Ltac xrun HS HJ SHOK :=
lazymatch type of HS with
| st_ok _ ?E ?ss (restrict (w_H ?W) ?ms) =>
lazymatch type of SHOK with
| sh_ok _ ?Bx ?SH _ _ =>
let K := eval vm_compute in (run_K 36 Bx SH ss) in
let res := eval vm_compute in (sym_runN_tok rsegs hex4_tbl K Bx XSPAN SH 200000%N ss) in
lazymatch res with
| (?st', ?rs) =>
let Hrun := fresh "Hrun" in
assert (Hrun : sym_runN_tok rsegs hex4_tbl K Bx XSPAN SH 200000%N ss = (st', rs)) by (vm_compute; reflexivity);
eapply (RUN W 200000%N E K Bx XSPAN SH ss st' rs ms);
[ exact HS | exact SHOK | vm_compute; reflexivity | exact Hrun | exact I | exact HJ
| clear Hrun; cbn [sh_obls]; apply Forall_nil | clear Hrun | clear Hrun HS HJ SHOK ]
end end end.
Ltac xrunto stop HS HJ SHOK :=
lazymatch type of HS with
| st_ok _ ?E ?ss (restrict (w_H ?W) ?ms) =>
lazymatch type of SHOK with
| sh_ok _ ?Bx ?SH _ _ =>
let K := eval vm_compute in (run_K 36 Bx SH ss) in
let res := eval vm_compute in (sym_run_toN_tok rsegs hex4_tbl K Bx XSPAN SH 200000%N stop ss) in
lazymatch res with
| (?st', ?rs) =>
let Hrun := fresh "Hrun" in
assert (Hrun : sym_run_toN_tok rsegs hex4_tbl K Bx XSPAN SH 200000%N stop ss = (st', rs)) by (vm_compute; reflexivity);
eapply (RUNTO W 200000%N stop E K Bx XSPAN SH ss st' rs ms);
[ exact HS | exact SHOK | vm_compute; reflexivity | exact Hrun | exact I | exact HJ
| clear Hrun; cbn [sh_obls]; apply Forall_nil | clear Hrun | clear Hrun HS HJ SHOK ]
end end end.
Ltac xafter HS HJ SHOK :=
let ws := fresh "ws" in let ms' := fresh "msx" in let mat' := fresh "mat" in
let Hlen := fresh "Hlen" in let HF := fresh "HF" in let HFr := fresh "HFr" in let HG := fresh "HG" in
intros ws ms' mat' Hlen HS SHOK HJ HF HFr HG;
cbn [sh_j sh_ss] in Hlen, HS, SHOK;
repeat (destruct ws as [|? ws]; [discriminate Hlen | cbn [length] in Hlen; injection Hlen as Hlen]);
(destruct ws; [clear Hlen | discriminate Hlen]);
cbn [extK length Nat.add] in HS, SHOK;
cbn [ms_mem mkst] in HF, HFr, HG, HJ.
Ltac xbr cnd a b HS Hc := apply (SRr_sym_branch rsegs _ _ _ _ _ _ cnd a b HS); clear HS; intros Hc HS.
Ltac prreg_raw HS r Hr :=
lazymatch type of HS with
| st_ok ?segs ?E ?ss (restrict ?H ?ms) =>
pose proof (st_ok_restrict_reg segs H E ss ms r HS) as Hr;
let e := eval vm_compute in (sr_get (ss_regs ss) r) in change (sr_get (ss_regs ss) r) with e in Hr;
cbn [ms_regs restrict mkst] in Hr
end.
Ltac zcond H :=
rewrite ?branch_geu_U, ?branch_ltu_U, ?branch_ne_U, ?branch_eq_U in H;
rewrite ?U_SOff, ?U_SLit in H;
repeat (rewrite ew_ewset_other in H by lia);
repeat match goal with
| H' : negb _ = true |- _ => apply negb_true_iff in H'
| H' : negb _ = false |- _ => apply negb_false_iff in H'
| H' : (_ <? _) = true |- _ => apply Z.ltb_lt in H'
| H' : (_ <? _) = false |- _ => apply Z.ltb_ge in H'
| H' : (_ =? _) = true |- _ => apply Z.eqb_eq in H'
| H' : (_ =? _) = false |- _ => apply Z.eqb_neq in H'
end;
unfold zcanon, M64 in H.
Definition turn_regs_ok (regs : bvmap 5 word) (p i o v sp : Z) : Prop :=
getr regs 2 = w64 sp /\ getr regs 5 = w64 6 /\ getr regs 6 = w64 5 /\ getr regs 7 = w64 (p + i) /\
getr regs 10 = w64 p /\ getr regs 11 = w64 o /\ getr regs 12 = w64 (p + i) /\ getr regs 13 = w64 v /\
getr regs 14 = w64 SHADOW_OFF /\ getr regs 15 = w64 (4 - i) /\ getr regs 16 = w64 1 /\ getr regs 17 = w64 10.
Ltac xafter2 W HKEEP HGROW HS HJ SHOK :=
let ws := fresh "ws" in let ms' := fresh "msx" in let mat' := fresh "mat" in let Hlen := fresh "Hlen" in
let HFa := fresh "HFa" in let HFb := fresh "HFb" in let HGc := fresh "HGc" in
let HK2 := fresh "HK2" in let HG2 := fresh "HG2" in
intros ws ms' mat' Hlen HS SHOK HJ HFa HFb HGc;
cbn [sh_j sh_ss] in Hlen, HS, SHOK;
repeat (destruct ws as [|? ws]; [discriminate Hlen | cbn [length] in Hlen; injection Hlen as Hlen]);
(destruct ws; [clear Hlen | discriminate Hlen]);
cbn [extK length Nat.add] in HS, SHOK;
cbn [ms_mem mkst] in HFa, HFb, HGc, HJ;
pose proof (keeps_trans W _ _ _ HKEEP (keeps_of_frame W _ _ _ _ (no_wrange_lc _) HFb)) as HK2;
clear HKEEP; rename HK2 into HKEEP;
pose proof (mem_grows_trans _ _ _ HGROW HGc) as HG2;
clear HGROW; rename HG2 into HGROW;
clear HFa HFb HGc.
Ltac kept_at regs0 extra0 HS HAE HKK :=
pose proof (regs_kept_of_st_ok rsegs _ _ _ regs0 extra0 HEX4_KEPT HS
ltac:(env_agree_chain HAE) ltac:(vm_compute; reflexivity)) as HKK;
cbn [ms_regs restrict] in HKK.
Ltac acc_tac cc vv delta U33 U34 :=
apply (acc_or _ 33 34 cc vv delta);
[ repeat (rewrite ew_ewset_other by lia); exact U33
| repeat (rewrite ew_ewset_other by lia); exact U34
| lia | lia ].
Ltac cnt_tac ii Hcnt U35 :=
zcond Hcnt; rewrite U35 in Hcnt;
rewrite (Z.mod_small (4 - ii + -1)) in Hcnt by lia; rewrite (Z.mod_small 0) in Hcnt by lia; lia.
Ltac xtail W regs0 extra0 pp ii cc vv delta KS KE E2 E10 E11 E14 U32 U33 U34 U35 HAE HKEEP HGROW HS HJ SHOK :=
let Hcnt := fresh "Hcnt" in
let Q2 := fresh "Q2" in let Q5 := fresh "Q5" in let Q6 := fresh "Q6" in let Q7 := fresh "Q7" in
let Q10 := fresh "Q10" in let Q11 := fresh "Q11" in let Q12 := fresh "Q12" in let Q13 := fresh "Q13" in
let Q14 := fresh "Q14" in let Q15 := fresh "Q15" in let Q16 := fresh "Q16" in let Q17 := fresh "Q17" in
let HKK := fresh "HKK" in
xrunto (HEX4_B + 0xa0) HS HJ SHOK; [ apply awr_ok_lc | ];
xafter2 W HKEEP HGROW HS HJ SHOK;
xbr BC_NE (SOff 35 (-1)) (SLit 0) HS Hcnt;
[ xrunto (HEX4_B + 0x34) HS HJ SHOK; [ apply awr_ok_lc | ];
xafter2 W HKEEP HGROW HS HJ SHOK;
prreg HS (2%bv : bv 5) Q2; prreg HS (5%bv : bv 5) Q5; prreg HS (6%bv : bv 5) Q6;
prreg HS (7%bv : bv 5) Q7; prreg HS (10%bv : bv 5) Q10; prreg HS (11%bv : bv 5) Q11;
prreg HS (12%bv : bv 5) Q12; prreg_raw HS (13%bv : bv 5) Q13; prreg HS (14%bv : bv 5) Q14;
prreg HS (15%bv : bv 5) Q15; prreg HS (16%bv : bv 5) Q16; prreg HS (17%bv : bv 5) Q17;
kept_at regs0 extra0 HS HAE HKK; pmkst HS;
eapply (KS (cc + delta));
[ hexval_solve | cnt_tac ii Hcnt U35 | exact HKEEP | exact HGROW | exact HJ
| unfold turn_regs_ok; repeat split;
  [ rewrite Q2, E2; reflexivity | rewrite Q5; reflexivity | rewrite Q6; reflexivity
  | rewrite Q7, U32; unfold w64; f_equal; lia
  | rewrite Q10, E10; reflexivity | rewrite Q11, E11; reflexivity
  | rewrite Q12, U32; unfold w64; f_equal; lia
  | rewrite Q13; acc_tac cc vv delta U33 U34
  | rewrite Q14, E14; reflexivity
  | rewrite Q15, U35; unfold w64; f_equal; lia
  | rewrite Q16; reflexivity | rewrite Q17; reflexivity ]
| exact HKK ]
| xrunto (HEX4_B + 0xb8) HS HJ SHOK; [ apply awr_ok_lc | ];
xafter2 W HKEEP HGROW HS HJ SHOK;
prreg HS (2%bv : bv 5) Q2; prreg HS (11%bv : bv 5) Q11; prreg_raw HS (13%bv : bv 5) Q13;
prreg HS (14%bv : bv 5) Q14; kept_at regs0 extra0 HS HAE HKK; pmkst HS;
eapply (KE (cc + delta));
[ hexval_solve | cnt_tac ii Hcnt U35 | exact HKEEP | exact HGROW | exact HJ
| rewrite Q2, E2; reflexivity | rewrite Q11, E11; reflexivity | rewrite Q13; acc_tac cc vv delta U33 U34
| rewrite Q14, E14; reflexivity | exact HKK ] ].
Lemma entry_st_ok_full : forall E pc sr regs (rs : smem) (G : facts) mem,
regs_ok E sr regs -> regions_wf rs = true -> Forall (region_ok rsegs E mem) rs -> pairwise_disjoint E rs -> facts_ok E G ->
st_ok rsegs E (mkSS pc sr rs None G) (mkst regs (Z_to_bv 64 pc) mem (seg_rom rsegs)).
Proof.
intros E pc sr regs rs G mem Hsr Hwf Hrs Hpd HG.
unfold st_ok. cbn [ms_fregs ms_pc_val ms_svc_pending ms_resv ms_fcsr ms_rom ms_regs ms_mem mkst
ss_pc ss_regs ss_mem ss_resv ss_facts resv_denot].
repeat (split; [reflexivity|]). split; [exact Hsr|]. split; [| exact HG]. split; [exact Hwf|]. split; [exact Hrs | exact Hpd].
Qed.
Lemma hex4_entry_ok : forall (W : world rsegs) regs memc mdc ly S Hp p o sp,
ARx ly S Hp W memc mdc ->
getr regs 2 = w64 sp -> 2 ^ 46 <= sp - 16 -> sp <= 2 ^ 47 -> sp mod 16 = 0 ->
getr regs 10 = w64 p -> getr regs 11 = w64 o ->
hex4_src_ok p -> hex4_out_ok o -> o mod 4 = 0 ->
range_addressable (aview rsegs (w_H W) memc) SHADOW_OFF p 4 ->
range_addressable (aview rsegs (w_H W) memc) SHADOW_OFF o 4 ->
(forall x, sp - 16 <= x < sp -> apresent (w_H W) memc x) ->
st_ok rsegs (Ereg regs [w64 SHADOW_OFF]) ss_e
(restrict (w_H W) (mkst regs (w64 HEX4_B) memc (seg_rom rsegs)))
/\ sh_ok rsegs XBx SHe (Ereg regs [w64 SHADOW_OFF]) (mrestrict (w_H W) memc).
Proof.
intros W regs memc mdc ly S Hp p o sp HAR R2 Hsp0 Hsp1 Hsp16 R10 R11 HPa HOa HOal RAp RAo HPres.
pose proof (alx_const rsegs B ARx LAWS ly S Hp W memc mdc HAR) as (Kcell & _ & Kgot & _).
rewrite HGOT, HCELL in Kgot. rewrite HCELL in Kcell.
destruct HPa as (HPlo & HPhi). destruct HOa as (HOlo & HOhi).
pose proof (hex4_obj_img 0 ltac:(lia)) as Hgi. pose proof (hex4_obj_img 12 ltac:(lia)) as Hci.
change (hex4_val (A_OBJ 0)) with GOT_SHADOW_B in Hgi. change (hex4_val (A_OBJ 12)) with SHADOW_CELL_B in Hci.
assert (Hgc : GOT_SHADOW_B + 8 <= SHADOW_CELL_B \/ SHADOW_CELL_B + 8 <= GOT_SHADOW_B) by exact (palc_got_cell B TL).
rewrite IMG_LO_B_val, IMG_TOP_B_val in Hgi, Hci.
pose proof (proj1 (@ASAN_CEIL_range _)) as HCEIL.
set (E := Ereg regs [w64 SHADOW_OFF]).
assert (E2 : ew E 2 = w64 sp) by (unfold E; rewrite (ew_Ereg_nat regs _ 2 2%bv eq_refl); exact R2).
assert (E10 : ew E 10 = w64 p) by (unfold E; rewrite (ew_Ereg_nat regs _ 10 10%bv eq_refl); exact R10).
assert (E11 : ew E 11 = w64 o) by (unfold E; rewrite (ew_Ereg_nat regs _ 11 11%bv eq_refl); exact R11).
assert (E32 : ew E 32 = w64 SHADOW_OFF) by (unfold E; exact (ew_Ereg_extra regs _ 0)).
assert (U2 : bv_unsigned (ew E 2) = sp) by (rewrite E2; apply unsigned_lit_small; unfold kLowShadowBeg, kHighMemBeg in *; lia).
assert (U10 : bv_unsigned (ew E 10) = p) by (rewrite E10; apply unsigned_lit_small; unfold kLowShadowBeg, kHighMemBeg in *; lia).
assert (U11 : bv_unsigned (ew E 11) = o) by (rewrite E11; apply unsigned_lit_small; unfold kLowShadowBeg, kHighMemBeg in *; lia).
assert (U32 : bv_unsigned (ew E 32) = SHADOW_OFF) by (rewrite E32; apply unsigned_lit_small; unfold SHADOW_OFF; lia).
assert (UBx : U E XBx = SHADOW_OFF) by (unfold XBx; apply (U_atom E 32 SHADOW_OFF E32); unfold SHADOW_OFF; lia).
split.
- rewrite restrict_mkst_fx. unfold ss_e. change (w64 HEX4_B) with (Z_to_bv 64 HEX4_B).
apply entry_st_ok_full.
+ unfold E. apply regs_ok_Ereg.
+ vm_compute. reflexivity.
+ repeat apply Forall_cons; try apply Forall_nil; unfold region_ok, stkE, gotR, cellR;
cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
* rewrite U2. split; [lia|]. split; [lia|]. split; [|constructor].
intros x Hx. apply (apresent_writable rsegs). apply HPres. lia.
* split; [lia|]. split; [lia|]. split; [intros x Hx; lia|].
constructor; [|constructor].
apply (chunk_ok_val rsegs E _ 0 GOT_SHADOW_B 8 (SLit SHADOW_CELL_B) SHADOW_CELL_B);
[cbn [sv_denot]; reflexivity | lia | lia |].
rewrite Z.add_0_l. exact (val_mem_of_rdword rsegs (w_H W) memc _ _ Kgot).
* split; [lia|]. split; [lia|]. split; [intros x Hx; lia|].
constructor; [|constructor].
apply (chunk_ok_val rsegs E _ 0 SHADOW_CELL_B 8 (SOff 32 0) SHADOW_OFF);
[cbn [sv_denot]; rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | unfold SHADOW_OFF; lia | lia |].
rewrite Z.add_0_l. exact (val_mem_of_rdword rsegs (w_H W) memc _ _ Kcell).
+ apply pairwise_disjoint_of_extents. unfold stkE, gotR, cellR, extent_of_region.
cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite U2.
cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
repeat split; lia.
+ split; [|split; [exact I | exact I]].
cbn [f_atoms atoms_ok]. unfold afact_ok, SRCx, OUTx, SPfact, SBfact. cbn [af_lo af_hi af_al2].
rewrite U2, U10, U11, U32. change (2 ^ 4) with 16. change (2 ^ 0) with 1. change (2 ^ 2) with 4.
rewrite !Z.mod_1_r. unfold SHADOW_OFF, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in *.
repeat match goal with |- _ /\ _ => split end; lia.
- unfold sh_ok, SHe. constructor; [|constructor; [|constructor]].
+ apply (shent_ok_of_range rsegs (w_H W) memc E XBx 10 p 4 p 0 4 RAp UBx);
[apply (U_atom E 10 p E10); unfold kLowShadowBeg, kHighMemBeg in *; lia | lia | lia |].
intros x Hx. cbn [Z.min Z.max] in Hx. unfold SHADOW_OFF, kLowShadowBeg, kHighMemBeg in *. lia.
+ apply (shent_ok_of_range rsegs (w_H W) memc E XBx 11 o 4 o 0 4 RAo UBx);
[apply (U_atom E 11 o E11); unfold kLowShadowBeg, kHighMemBeg in *; lia | lia | lia |].
intros x Hx. cbn [Z.min Z.max] in Hx. unfold SHADOW_OFF, kLowShadowBeg, kHighMemBeg in *. lia.
Qed.
Lemma hex4_final : forall (W : world rsegs) regs memc mdc STK sp0 FP ly S Hp W0 mem0 md0 own lyc Sc Hpc k o sp h ra0,
ajournal_x (SK := SK) rsegs B PST ARx STK sp0 FP ly S Hp W0 mem0 md0 own lyc Sc Hpc W memc mdc k ->
getr regs 1 = w64 ra0 -> 4096 <= ra0 < 2 ^ 64 -> ra0 mod 2 = 0 ->
getr regs 2 = w64 sp -> getr regs 11 = w64 o -> getr regs 13 = w64 h -> getr regs 14 = w64 SHADOW_OFF ->
0 <= h < 65536 ->
sp mod 16 = 0 -> 2 ^ 46 <= sp -> sp + 16 <= 2 ^ 47 -> sp0 - STK <= sp -> sp + 16 <= sp0 ->
val_mem rsegs (mrestrict (w_H W) memc) (sp + 8) 8 ra0 ->
hex4_out_ok o -> o mod 4 = 0 -> range_addressable (aview rsegs (w_H W) memc) SHADOW_OFF o 4 ->
(forall x, o <= x < o + 4 -> awr_byte STK sp0 FP (ablocks B ly S) (ablocks B lyc Sc) lyc own x) ->
(forall x, o <= x < o + 4 -> apresent (w_H W) memc x) ->
(sp + 16 <= o \/ o + 4 <= sp) ->
SRr rsegs W (mkCfg (mkst regs (w64 (HEX4_B + 0xb8)) memc (seg_rom rsegs)) mdc)
(fun W' c' => W' = W /\ exists regs' mem' md',
c' = mkCfg (mkst regs' (getr regs 1) mem' (seg_rom rsegs)) md' /\
ajournal_x (SK := SK) rsegs B PST ARx STK sp0 FP ly S Hp W0 mem0 md0 own lyc Sc Hpc W mem' md' k /\
(forall r, In r HEX4_KEPT -> getr regs' r = getr regs r) /\
getr regs' 2 = w64 (sp + 16) /\ getr regs' 10 = w64 0 /\
val_mem rsegs (mrestrict (w_H W) mem') o 4 h /\
(forall x, 0 <= x < 2 ^ 64 -> ~ (o <= x < o + 4) -> aview rsegs (w_H W) mem' x = aview rsegs (w_H W) memc x)).
Proof.
intros W regs memc mdc STK sp0 FP ly S Hp W0 mem0 md0 own lyc Sc Hpc k o sp h ra0
HJ R1 Hra Hra2 R2 R11 R13 R14 Hh Hsp16 Hsplo Hsphi Hsp0a Hsp0b Mra HOa HOal RAo HAWR HOpres HOsep.
pose proof (proj1 (@ASAN_CEIL_range _)) as HCEIL.
destruct HOa as (HOlo & HOhi).
set (E := Ereg regs [w64 h]).
assert (E1 : ew E 1 = w64 ra0) by (unfold E; rewrite (ew_Ereg_nat regs _ 1 1%bv eq_refl); exact R1).
assert (E2 : ew E 2 = w64 sp) by (unfold E; rewrite (ew_Ereg_nat regs _ 2 2%bv eq_refl); exact R2).
assert (E11 : ew E 11 = w64 o) by (unfold E; rewrite (ew_Ereg_nat regs _ 11 11%bv eq_refl); exact R11).
assert (E14 : ew E 14 = w64 SHADOW_OFF) by (unfold E; rewrite (ew_Ereg_nat regs _ 14 14%bv eq_refl); exact R14).
assert (E32 : ew E 32 = w64 h) by (unfold E; exact (ew_Ereg_extra regs _ 0)).
assert (U1 : bv_unsigned (ew E 1) = ra0) by (rewrite E1; apply unsigned_lit_small; lia).
assert (U2 : bv_unsigned (ew E 2) = sp) by (rewrite E2; apply unsigned_lit_small; lia).
assert (U11 : bv_unsigned (ew E 11) = o) by (rewrite E11; apply unsigned_lit_small; unfold kLowShadowBeg, kHighMemBeg in *; lia).
assert (U14 : bv_unsigned (ew E 14) = SHADOW_OFF) by (rewrite E14; apply unsigned_lit_small; unfold SHADOW_OFF; lia).
assert (U32 : bv_unsigned (ew E 32) = h) by (rewrite E32; apply unsigned_lit_small; lia).
assert (UBx : U E XBxL = SHADOW_OFF) by (unfold XBxL; apply (U_atom E 14 SHADOW_OFF E14); unfold SHADOW_OFF; lia).
assert (HS : st_ok rsegs E ss_f (restrict (w_H W) (mkst regs (w64 (HEX4_B + 0xb8)) memc (seg_rom rsegs)))).
{ rewrite restrict_mkst_fx. unfold ss_f. unfold w64 at 1. apply entry_st_ok_full.
- unfold fin_regs. apply regs_ok_pin; [unfold E; apply regs_ok_Ereg | discriminate |].
cbn [sv_denot]. rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned. exact R13.
- vm_compute. reflexivity.
- repeat apply Forall_cons; try apply Forall_nil; unfold region_ok, stkL, outR;
cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
+ rewrite U2. split; [lia|]. split; [lia|]. split; [intros x Hx; lia|].
constructor; [|constructor].
apply (chunk_ok_val rsegs E _ sp 8 8 (SOff 1 0) ra0);
[cbn [sv_denot]; rewrite E1, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | lia | lia | exact Mra].
+ rewrite U11. split; [unfold kLowShadowBeg, kHighMemBeg in *; lia|].
split; [unfold kLowShadowBeg, kHighMemBeg in *; lia|]. split; [|constructor].
intros x Hx. apply (apresent_writable rsegs). apply HOpres. lia.
- apply pairwise_disjoint_of_extents. unfold stkL, outR, extent_of_region.
cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite U2, U11.
cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd]. repeat split; lia.
- split; [|split; [exact I | exact I]].
cbn [f_atoms atoms_ok]. unfold afact_ok, OUTx, SPfact, SBfact. cbn [af_lo af_hi af_al2].
rewrite U2, U11, U14, U32. change (2 ^ 4) with 16. change (2 ^ 0) with 1. change (2 ^ 2) with 4.
rewrite !Z.mod_1_r. unfold SHADOW_OFF, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in *.
repeat match goal with |- _ /\ _ => split end; lia. }
assert (SHOK : sh_ok rsegs XBxL SHf E (mrestrict (w_H W) memc)).
{ unfold sh_ok, SHf. constructor; [|constructor].
apply (shent_ok_of_range rsegs (w_H W) memc E XBxL 11 o 4 o 0 4 RAo UBx);
[apply (U_atom E 11 o E11); unfold kLowShadowBeg, kHighMemBeg in *; lia | lia | lia |].
intros x Hx. cbn [Z.min Z.max] in Hx. unfold SHADOW_OFF, kLowShadowBeg, kHighMemBeg in *. lia. }
xrun HS HJ SHOK.
{ intros a (r & Hin & Hr); cbn [ss_mem ss_f In] in Hin;
destruct Hin as [<-|[<-|[]]]; unfold stkL, outR in Hr;
cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi base_val] in Hr;
[ rewrite U2 in Hr; lia | rewrite U11 in Hr; apply HAWR; lia ]. }
intros ws ms' mat' Hlen HS' SHOK' HJ' HF HFr HG.
cbn [sh_j sh_ss] in Hlen, HS', SHOK'.
repeat (destruct ws as [|? ws]; [discriminate Hlen | cbn [length] in Hlen; injection Hlen as Hlen]).
destruct ws; [clear Hlen | discriminate Hlen].
cbn [extK length Nat.add] in HS', SHOK'.
cbn [ms_mem mkst] in HF, HFr, HG, HJ'.
prreg HS' (1%bv : bv 5) P1. prreg HS' (2%bv : bv 5) P2. prreg HS' (10%bv : bv 5) P10.
assert (HAE : env_agree 32 (Ereg regs [w64 h]) E) by (unfold E; apply env_agree_refl).
pose proof (regs_kept_of_st_ok rsegs _ _ _ regs [w64 h] HEX4_KEPT HS' ltac:(env_agree_chain HAE)
ltac:(vm_compute; reflexivity)) as HK.
cbn [ms_regs restrict] in HK, P1, P2, P10.
pose proof (st_ok_region_nth _ _ _ 1%nat
(YP09.mkRegion (Some 11%nat) 0 4 0 4 [YP09.mkChunk 0 (CVal 4 (SOff 32 0))]) HS' eq_refl) as HRout.
destruct HRout as (_ & _ & _ & Hcs).
eapply (RET W _ _ _ _ _ HS' eq_refl ltac:(vm_compute; reflexivity)).
intros mat2. clear HS' SHOK' HF HG. srr_norm_model.
cbn [YP09.r_base YP09.r_chunks YP09.c_off YP09.c_val base_val] in Hcs.
rewrite !ew_ewset_other in Hcs by lia. rewrite U11 in Hcs.
pose proof (proj1 (Forall_forall _ _) Hcs _ ltac:(left; reflexivity)) as Hchunk. clear Hcs.
split; [reflexivity|].
lazymatch goal with |- exists _ _ _, mkCfg (mkst ?r _ ?m _) ?d = _ /\ _ => exists r, m, d end.
split; [cbn [ms_regs]; rewrite P1, E1, R1; unfold w64;
rewrite (v_jalr_lit_even ra0 ltac:(lia) Hra2); reflexivity|].
split; [pose proof (ajournal_x_materialize rsegs B PST ARx LAWS img_segs_low _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ mat2 HJ') as HJ2;
rewrite wvb_collapse in HJ2; exact HJ2|].
split; [exact HK|].
split; [cbn [ms_regs]; rewrite P2, U2; reflexivity|].
split; [cbn [ms_regs]; rewrite P10; reflexivity|].
split.
- cbn [ms_mem restrict] in Hchunk |- *.
assert (HV : val_mem rsegs (mrestrict (w_H W) (ms_mem ms')) (o + 0) (N.to_nat 4) h).
{ lazymatch type of Hchunk with YP09.chunk_ok _ ?EE _ _ _ =>
apply (val_of_chunk_ok rsegs EE _ o 0 4 (SOff 32 0) h) end;
[ exact Hchunk
| cbn [sv_denot]; rewrite !ew_ewset_other by lia; rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
| cbn; lia | lia]. }
cbn [N.to_nat Pos.to_nat Pos.iter_op Nat.add] in HV. rewrite Z.add_0_r in HV. exact HV.
- intros x Hx Hnot. cbn [ms_mem].
apply (frame_aview E (ss_mem ss_f) memc _ (w_H W) x HFr Hx).
intros (r & Hin & Hr). cbn [ss_mem ss_f In] in Hin.
destruct Hin as [<-|[<-|[]]]; unfold stkL, outR in Hr;
cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi base_val] in Hr;
[ rewrite U2 in Hr; lia | rewrite U11 in Hr; apply Hnot; lia ].
Qed.
Lemma hex4_failret : forall (W : world rsegs) regs memc mdc STK sp0 FP ly S Hp W0 mem0 md0 own lyc Sc Hpc k sp ra0,
ajournal_x (SK := SK) rsegs B PST ARx STK sp0 FP ly S Hp W0 mem0 md0 own lyc Sc Hpc W memc mdc k ->
getr regs 1 = w64 ra0 -> 4096 <= ra0 < 2 ^ 64 -> ra0 mod 2 = 0 -> getr regs 2 = w64 sp ->
sp mod 16 = 0 -> 2 ^ 46 <= sp -> sp + 16 <= 2 ^ 47 ->
val_mem rsegs (mrestrict (w_H W) memc) (sp + 8) 8 ra0 ->
SRr rsegs W (mkCfg (mkst regs (w64 (HEX4_B + 0xdc)) memc (seg_rom rsegs)) mdc)
(fun W' c' => W' = W /\ exists regs' mem' md',
c' = mkCfg (mkst regs' (getr regs 1) mem' (seg_rom rsegs)) md' /\
ajournal_x (SK := SK) rsegs B PST ARx STK sp0 FP ly S Hp W0 mem0 md0 own lyc Sc Hpc W mem' md' k /\
(forall r, In r HEX4_KEPT -> getr regs' r = getr regs r) /\
getr regs' 2 = w64 (sp + 16) /\ getr regs' 10 = w64 (-1) /\ keeps W memc mem').
Proof.
intros W regs memc mdc STK sp0 FP ly S Hp W0 mem0 md0 own lyc Sc Hpc k sp ra0
HJ R1 Hra Hra2 R2 Hsp16 Hsplo Hsphi Mra.
set (E := Ereg regs (@nil word)).
assert (E1 : ew E 1 = w64 ra0) by (unfold E; rewrite (ew_Ereg_nat regs _ 1 1%bv eq_refl); exact R1).
assert (E2 : ew E 2 = w64 sp) by (unfold E; rewrite (ew_Ereg_nat regs _ 2 2%bv eq_refl); exact R2).
assert (U2 : bv_unsigned (ew E 2) = sp) by (rewrite E2; apply unsigned_lit_small; lia).
assert (HS : st_ok rsegs E ss_q (restrict (w_H W) (mkst regs (w64 (HEX4_B + 0xdc)) memc (seg_rom rsegs)))).
{ rewrite restrict_mkst_fx. unfold ss_q. unfold w64 at 1. apply entry_st_ok_full.
- unfold E. apply regs_ok_Ereg.
- vm_compute. reflexivity.
- repeat apply Forall_cons; try apply Forall_nil; unfold region_ok, stkL;
cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
rewrite U2. split; [lia|]. split; [lia|]. split; [intros x Hx; lia|].
constructor; [|constructor].
apply (chunk_ok_val rsegs E _ sp 8 8 (SOff 1 0) ra0);
[cbn [sv_denot]; rewrite E1, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | lia | lia | exact Mra].
- cbn [pairwise_disjoint all_disjoint]. repeat split.
- split; [|split; [exact I | exact I]].
cbn [f_atoms atoms_ok]. unfold afact_ok, SPfact. cbn [af_lo af_hi af_al2].
rewrite U2. change (2 ^ 4) with 16. repeat match goal with |- _ /\ _ => split end; lia. }
assert (SHOK : sh_ok rsegs XBxL (@nil shent) E (mrestrict (w_H W) memc)) by (unfold sh_ok; apply Forall_nil).
xrun HS HJ SHOK.
{ intros a (r & Hin & Hr); cbn [ss_mem ss_q In] in Hin;
destruct Hin as [<-|[]]; unfold stkL in Hr;
cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi base_val] in Hr; lia. }
xafter HS' HJ' SHOK'.
prreg HS' (1%bv : bv 5) P1. prreg HS' (2%bv : bv 5) P2. prreg HS' (10%bv : bv 5) P10.
assert (HAE : env_agree 32 (Ereg regs (@nil word)) E) by (unfold E; apply env_agree_refl).
pose proof (regs_kept_of_st_ok rsegs _ _ _ regs (@nil word) HEX4_KEPT HS' ltac:(env_agree_chain HAE)
ltac:(vm_compute; reflexivity)) as HK.
cbn [ms_regs restrict] in HK, P1, P2, P10.
eapply (RET W _ _ _ _ _ HS' eq_refl ltac:(vm_compute; reflexivity)).
intros mat2. clear HS' SHOK' HF HG. srr_norm_model.
split; [reflexivity|].
lazymatch goal with |- exists _ _ _, mkCfg (mkst ?r _ ?m _) ?d = _ /\ _ => exists r, m, d end.
split; [cbn [ms_regs]; rewrite P1, E1, R1; unfold w64;
rewrite (v_jalr_lit_even ra0 ltac:(lia) Hra2); reflexivity|].
split; [pose proof (ajournal_x_materialize rsegs B PST ARx LAWS img_segs_low _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ mat2 HJ') as HJ2;
rewrite wvb_collapse in HJ2; exact HJ2|].
split; [exact HK|].
split; [cbn [ms_regs]; rewrite P2, U2; reflexivity|].
split; [cbn [ms_regs]; rewrite P10; apply bv_eq; vm_compute; reflexivity|].
intros x Hx. cbn [ms_mem].
apply (frame_aview E (ss_mem ss_q) memc _ (w_H W) x HFr Hx).
intros (r & Hin & Hr). cbn [ss_mem ss_q In] in Hin.
destruct Hin as [<-|[]]; unfold stkL in Hr;
cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi base_val] in Hr; lia.
Qed.
Lemma hex4_turn : forall (W : world rsegs) regs memc mdc STK sp0 FP ly S Hp W0 mem0 md0 own lyc Sc Hpc k
p o sp ra0 i v c (Q : world rsegs -> config -> Prop),
ajournal_x (SK := SK) rsegs B PST ARx STK sp0 FP ly S Hp W0 mem0 md0 own lyc Sc Hpc W memc mdc k ->
0 <= i <= 3 -> 0 <= v < 4096 -> 0 <= c < 256 ->
getr regs 1 = w64 ra0 -> 4096 <= ra0 < 2 ^ 64 ->
turn_regs_ok regs p i o v sp ->
sp mod 16 = 0 -> 2 ^ 46 <= sp -> sp + 16 <= 2 ^ 47 ->
val_mem rsegs (mrestrict (w_H W) memc) (sp + 8) 8 ra0 ->
hex4_src_ok p -> range_addressable (aview rsegs (w_H W) memc) SHADOW_OFF p 4 ->
val_mem rsegs (mrestrict (w_H W) memc) (p + i) 1 c ->
hex4_out_ok o -> o mod 4 = 0 -> range_addressable (aview rsegs (w_H W) memc) SHADOW_OFF o 4 ->
(sp + 16 <= p \/ p + 4 <= sp) ->
(forall d mem2 mdc2 regs2, PjGrammar.hexval c = Some d -> 4 - i - 1 <> 0 ->
keeps W memc mem2 -> mem_grows (mrestrict (w_H W) memc) (mrestrict (w_H W) mem2) ->
ajournal_x (SK := SK) rsegs B PST ARx STK sp0 FP ly S Hp W0 mem0 md0 own lyc Sc Hpc W mem2 mdc2 k ->
turn_regs_ok regs2 p (i + 1) o (16 * v + d) sp ->
(forall r, In r HEX4_KEPT -> getr regs2 r = getr regs r) ->
SRr rsegs W (mkCfg (mkst regs2 (w64 (HEX4_B + 0x34)) mem2 (seg_rom rsegs)) mdc2) Q) ->
(forall d mem2 mdc2 regs2, PjGrammar.hexval c = Some d -> 4 - i - 1 = 0 ->
keeps W memc mem2 -> mem_grows (mrestrict (w_H W) memc) (mrestrict (w_H W) mem2) ->
ajournal_x (SK := SK) rsegs B PST ARx STK sp0 FP ly S Hp W0 mem0 md0 own lyc Sc Hpc W mem2 mdc2 k ->
getr regs2 2 = w64 sp -> getr regs2 11 = w64 o -> getr regs2 13 = w64 (16 * v + d) ->
getr regs2 14 = w64 SHADOW_OFF ->
(forall r, In r HEX4_KEPT -> getr regs2 r = getr regs r) ->
SRr rsegs W (mkCfg (mkst regs2 (w64 (HEX4_B + 0xb8)) mem2 (seg_rom rsegs)) mdc2) Q) ->
(forall mem2 mdc2 regs2, PjGrammar.hexval c = None ->
keeps W memc mem2 -> mem_grows (mrestrict (w_H W) memc) (mrestrict (w_H W) mem2) ->
ajournal_x (SK := SK) rsegs B PST ARx STK sp0 FP ly S Hp W0 mem0 md0 own lyc Sc Hpc W mem2 mdc2 k ->
getr regs2 2 = w64 sp ->
(forall r, In r HEX4_KEPT -> getr regs2 r = getr regs r) ->
SRr rsegs W (mkCfg (mkst regs2 (w64 (HEX4_B + 0xdc)) mem2 (seg_rom rsegs)) mdc2) Q) ->
SRr rsegs W (mkCfg (mkst regs (w64 (HEX4_B + 0x34)) memc (seg_rom rsegs)) mdc) Q.
Proof.
intros W regs memc mdc STK sp0 FP ly S Hp W0 mem0 md0 own lyc Sc Hpc k p o sp ra0 i v c Q
HJ Hi Hv Hc256 R1 Hra (R2 & R5 & R6 & R7 & R10 & R11 & R12 & R13 & R14 & R15 & R16 & R17)
Hsp16 Hsplo Hsphi Mra HPa RAp Mc HOa HOal RAo Hsp_p KS KE KF.
pose proof (proj1 (@ASAN_CEIL_range _)) as HCEIL.
destruct HPa as (HPlo & HPhi).
destruct HOa as (HOlo & HOhi).
set (E := Ereg regs [w64 (p + i); w64 c; w64 v; w64 (4 - i)]).
assert (E1 : ew E 1 = w64 ra0) by (unfold E; rewrite (ew_Ereg_nat regs _ 1 1%bv eq_refl); exact R1).
assert (E2 : ew E 2 = w64 sp) by (unfold E; rewrite (ew_Ereg_nat regs _ 2 2%bv eq_refl); exact R2).
assert (E10 : ew E 10 = w64 p) by (unfold E; rewrite (ew_Ereg_nat regs _ 10 10%bv eq_refl); exact R10).
assert (E11 : ew E 11 = w64 o) by (unfold E; rewrite (ew_Ereg_nat regs _ 11 11%bv eq_refl); exact R11).
assert (E14 : ew E 14 = w64 SHADOW_OFF) by (unfold E; rewrite (ew_Ereg_nat regs _ 14 14%bv eq_refl); exact R14).
assert (E32 : ew E 32 = w64 (p + i)) by (unfold E; exact (ew_Ereg_extra regs _ 0)).
assert (E33 : ew E 33 = w64 c) by (unfold E; exact (ew_Ereg_extra regs _ 1)).
assert (E34 : ew E 34 = w64 v) by (unfold E; exact (ew_Ereg_extra regs _ 2)).
assert (E35 : ew E 35 = w64 (4 - i)) by (unfold E; exact (ew_Ereg_extra regs _ 3)).
assert (U2 : bv_unsigned (ew E 2) = sp) by (rewrite E2; apply unsigned_lit_small; lia).
assert (U10 : bv_unsigned (ew E 10) = p) by (rewrite E10; apply unsigned_lit_small; unfold kLowShadowBeg, kHighMemBeg in *; lia).
assert (U11 : bv_unsigned (ew E 11) = o) by (rewrite E11; apply unsigned_lit_small; unfold kLowShadowBeg, kHighMemBeg in *; lia).
assert (U14 : bv_unsigned (ew E 14) = SHADOW_OFF) by (rewrite E14; apply unsigned_lit_small; unfold SHADOW_OFF; lia).
assert (U32 : bv_unsigned (ew E 32) = p + i) by (rewrite E32; apply unsigned_lit_small; unfold kLowShadowBeg, kHighMemBeg in *; lia).
assert (U33 : bv_unsigned (ew E 33) = c) by (rewrite E33; apply unsigned_lit_small; lia).
assert (U34 : bv_unsigned (ew E 34) = v) by (rewrite E34; apply unsigned_lit_small; lia).
assert (U35 : bv_unsigned (ew E 35) = 4 - i) by (rewrite E35; apply unsigned_lit_small; lia).
assert (UBx : U E XBxL = SHADOW_OFF) by (unfold XBxL; apply (U_atom E 14 SHADOW_OFF E14); unfold SHADOW_OFF; lia).
assert (HS : st_ok rsegs E ss_l (restrict (w_H W) (mkst regs (w64 (HEX4_B + 0x34)) memc (seg_rom rsegs)))).
{ rewrite restrict_mkst_fx. unfold ss_l. unfold w64 at 1. apply entry_st_ok_full.
- unfold loop_regs.
repeat (apply regs_ok_pin; [|discriminate|cbn [sv_denot]; rewrite ?Z.add_0_r, ?Z_to_bv_bv_unsigned;
first [exact R12 | exact R7 | exact R15 | exact R16 | exact R17 | exact R5 | exact R6 | exact R13
| rewrite E32; reflexivity | rewrite E35; reflexivity | rewrite E34; reflexivity]]).
unfold E. apply regs_ok_Ereg.
- vm_compute. reflexivity.
- repeat apply Forall_cons; try apply Forall_nil; unfold region_ok, stkL, curR;
cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
+ rewrite U2. split; [lia|]. split; [lia|]. split; [intros x Hx; lia|].
constructor; [|constructor].
apply (chunk_ok_val rsegs E _ sp 8 8 (SOff 1 0) ra0);
[cbn [sv_denot]; rewrite E1, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | lia | lia | exact Mra].
+ rewrite U32. split; [unfold kLowShadowBeg, kHighMemBeg in *; lia|].
split; [unfold kLowShadowBeg, kHighMemBeg in *; lia|]. split; [intros x Hx; lia|].
constructor; [|constructor].
apply (chunk_ok_val rsegs E _ (p + i) 0 1 (SOff 33 0) c);
[cbn [sv_denot]; rewrite E33, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | cbn; lia | cbn; lia |].
rewrite Z.add_0_r. exact Mc.
- apply pairwise_disjoint_of_extents. unfold stkL, curR, extent_of_region.
cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite U2, U32.
cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd]. repeat split; lia.
- split; [|split; [exact I | exact I]].
cbn [f_atoms atoms_ok]. unfold afact_ok, SRCx, OUTx, SPfact, SBfact. cbn [af_lo af_hi af_al2].
rewrite U2, U10, U11, U14, U32, U33, U34, U35.
change (2 ^ 4) with 16. change (2 ^ 0) with 1. change (2 ^ 2) with 4. rewrite !Z.mod_1_r.
unfold SHADOW_OFF, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in *.
repeat match goal with |- _ /\ _ => split end; lia. }
assert (SHOK : sh_ok rsegs XBxL SHl E (mrestrict (w_H W) memc)).
{ unfold sh_ok, SHl. constructor; [|constructor; [|constructor]].
- apply (shent_ok_of_range rsegs (w_H W) memc E XBxL 32 p 4 (p + i) 0 1 RAp UBx);
[apply (U_atom E 32 (p + i) E32); unfold kLowShadowBeg, kHighMemBeg in *; lia | lia | lia |].
intros x Hx. cbn [Z.min Z.max] in Hx. unfold SHADOW_OFF, kLowShadowBeg, kHighMemBeg in *. lia.
- apply (shent_ok_of_range rsegs (w_H W) memc E XBxL 11 o 4 o 0 4 RAo UBx);
[apply (U_atom E 11 o E11); unfold kLowShadowBeg, kHighMemBeg in *; lia | lia | lia |].
intros x Hx. cbn [Z.min Z.max] in Hx. unfold SHADOW_OFF, kLowShadowBeg, kHighMemBeg in *. lia. }
assert (HAE : env_agree 32 (Ereg regs [w64 (p + i); w64 c; w64 v; w64 (4 - i)]) E)
by (unfold E; apply env_agree_refl).
assert (HKEEP : keeps W memc memc) by apply keeps_refl.
assert (HGROW : mem_grows (mrestrict (w_H W) memc) (mrestrict (w_H W) memc)) by apply mem_grows_refl.
xbr BC_LTU (SOff 32 0) (SOff 10 0) HS Hb1.
- exfalso. zcond Hb1. rewrite U32, U10 in Hb1.
rewrite (Z.mod_small (p + i + 0)) in Hb1 by (unfold kLowShadowBeg, kHighMemBeg in *; lia).
rewrite (Z.mod_small (p + 0)) in Hb1 by (unfold kLowShadowBeg, kHighMemBeg in *; lia). lia.
- clear Hb1. xrun HS HJ SHOK. { apply awr_ok_lc. } xafter2 W HKEEP HGROW HS HJ SHOK.
xbr BC_GEU (SOff 33 (-48)) (SLit 10) HS Hb2.
+
zcond Hb2. rewrite U33 in Hb2.
assert (Nd : ~ (0 <= c + (-48) < 10)) by (intros Hx; apply (proj2 (lt_mod_iff c (-48) 10 Hc256 ltac:(lia) ltac:(lia))) in Hx; lia).
clear Hb2.
xrun HS HJ SHOK. { apply awr_ok_lc. } xafter2 W HKEEP HGROW HS HJ SHOK.
xbr BC_GEU (SOff 33 (-97)) (SLit 6) HS Hb3.
*
zcond Hb3. rewrite U33 in Hb3.
assert (Nl : ~ (0 <= c + (-97) < 6)) by (intros Hx; apply (proj2 (lt_mod_iff c (-97) 6 Hc256 ltac:(lia) ltac:(lia))) in Hx; lia).
clear Hb3.
xrun HS HJ SHOK. { apply awr_ok_lc. } xafter2 W HKEEP HGROW HS HJ SHOK.
xbr BC_LTU (SLit 5) (SOff 33 (-65)) HS Hb4.
--
zcond Hb4. rewrite U33 in Hb4.
apply (proj1 (lt_mod_iff2 c (-65) 5 Hc256 ltac:(lia) ltac:(lia))) in Hb4.
xrunto (HEX4_B + 0xdc) HS HJ SHOK. { apply awr_ok_lc. } xafter2 W HKEEP HGROW HS HJ SHOK.
prreg HS (2%bv : bv 5) Q2. kept_at regs [w64 (p + i); w64 c; w64 v; w64 (4 - i)] HS HAE HKK.
pmkst HS.
eapply KF; [ hexval_solve | exact HKEEP | exact HGROW | exact HJ | rewrite Q2, E2; reflexivity | exact HKK ].
--
zcond Hb4. rewrite U33 in Hb4.
assert (Nu : 65 <= c <= 70)
by (assert (Hx : ~ (c + (-65) < 0 \/ 5 < c + (-65)))
by (intros Hy; apply (proj2 (lt_mod_iff2 c (-65) 5 Hc256 ltac:(lia) ltac:(lia))) in Hy; lia); lia).
clear Hb4.
xtail W regs [w64 (p + i); w64 c; w64 v; w64 (4 - i)] p i c v (-55) KS KE E2 E10 E11 E14 U32 U33 U34 U35 HAE HKEEP HGROW HS HJ SHOK.
*
zcond Hb3. rewrite U33 in Hb3.
apply (proj1 (lt_mod_iff c (-97) 6 Hc256 ltac:(lia) ltac:(lia))) in Hb3.
assert (Nu : 0 <= c + (-87) < 16) by lia.
xtail W regs [w64 (p + i); w64 c; w64 v; w64 (4 - i)] p i c v (-87) KS KE E2 E10 E11 E14 U32 U33 U34 U35 HAE HKEEP HGROW HS HJ SHOK.
+
zcond Hb2. rewrite U33 in Hb2.
apply (proj1 (lt_mod_iff c (-48) 10 Hc256 ltac:(lia) ltac:(lia))) in Hb2.
assert (Nu : 0 <= c + (-48) < 16) by lia.
xtail W regs [w64 (p + i); w64 c; w64 v; w64 (4 - i)] p i c v (-48) KS KE E2 E10 E11 E14 U32 U33 U34 U35 HAE HKEEP HGROW HS HJ SHOK.
Qed.
Definition loop_post (W : world rsegs) regs (STK sp0 : Z) FP ly S Hp W0 mem0 md0 own lyc Sc Hpc
(memc : word -> option byte) (k o sp : Z) (res : option Z) : world rsegs -> config -> Prop :=
fun W' c' => W' = W /\ exists regs' mem' md',
c' = mkCfg (mkst regs' (getr regs 1) mem' (seg_rom rsegs)) md' /\
ajournal_x (SK := SK) rsegs B PST ARx STK sp0 FP ly S Hp W0 mem0 md0 own lyc Sc Hpc W mem' md' k /\
(forall r, In r HEX4_KEPT -> getr regs' r = getr regs r) /\
getr regs' 2 = w64 (sp + 16) /\
(forall x, 0 <= x < 2 ^ 64 -> ~ (o <= x < o + 4) -> aview rsegs (w_H W) mem' x = aview rsegs (w_H W) memc x) /\
match res with
| Some h => getr regs' 10 = w64 0 /\ val_mem rsegs (mrestrict (w_H W) mem') o 4 h
| None => getr regs' 10 = w64 (-1) /\
(forall x, o <= x < o + 4 -> aview rsegs (w_H W) mem' x = aview rsegs (w_H W) memc x)
end.
Lemma hex4_loop : forall (n : nat) (i v : Z) (W : world rsegs) regs memc mdc
STK sp0 FP ly S Hp W0 mem0 md0 own lyc Sc Hpc k p o sp ra0 (rest : list Z),
Z.of_nat n = 3 - i -> 0 <= i <= 3 -> 0 <= v < 16 ^ i ->
ajournal_x (SK := SK) rsegs B PST ARx STK sp0 FP ly S Hp W0 mem0 md0 own lyc Sc Hpc W memc mdc k ->
getr regs 1 = w64 ra0 -> 4096 <= ra0 < 2 ^ 64 -> ra0 mod 2 = 0 ->
turn_regs_ok regs p i o v sp ->
sp mod 16 = 0 -> 2 ^ 46 <= sp -> sp + 16 <= 2 ^ 47 -> sp0 - STK <= sp -> sp + 16 <= sp0 ->
val_mem rsegs (mrestrict (w_H W) memc) (sp + 8) 8 ra0 ->
hex4_src_ok p -> range_addressable (aview rsegs (w_H W) memc) SHADOW_OFF p 4 ->
garr8 rsegs (mrestrict (w_H W) memc) (p + i) rest -> Z.of_nat (length rest) = 4 - i ->
hex4_out_ok o -> o mod 4 = 0 -> range_addressable (aview rsegs (w_H W) memc) SHADOW_OFF o 4 ->
(forall x, o <= x < o + 4 -> awr_byte STK sp0 FP (ablocks B ly S) (ablocks B lyc Sc) lyc own x) ->
(forall x, o <= x < o + 4 -> apresent (w_H W) memc x) ->
(sp + 16 <= p \/ p + 4 <= sp) -> (sp + 16 <= o \/ o + 4 <= sp) ->
SRr rsegs W (mkCfg (mkst regs (w64 (HEX4_B + 0x34)) memc (seg_rom rsegs)) mdc)
(loop_post W regs STK sp0 FP ly S Hp W0 mem0 md0 own lyc Sc Hpc memc k o sp (hacc v rest)).
Proof.
induction n as [|n IH]; intros i v W regs memc mdc STK sp0 FP ly S Hp W0 mem0 md0 own lyc Sc Hpc k p o sp ra0 rest
Hn Hi Hv HJ R1 Hra Hra2 TR Hsp16 Hsplo Hsphi Hsp0a Hsp0b Mra HPa RAp GBS Hlen HOa HOal RAo HAWR HOpres Hsp_p Hsp_o;
(pose proof (proj1 (@ASAN_CEIL_range _)) as HCEIL);
(pose proof HPa as (HPlo & HPhi));
(pose proof HOa as (HOlo & HOhi));
(destruct rest as [|c rest']; [cbn [length] in Hlen; exfalso; lia|]);
(destruct (garr8_hd W memc (p + i) c rest' GBS) as (Mc & Hc256));
(cbn [length] in Hlen);
(assert (Hvb : 0 <= v < 4096)
by (assert (16 ^ i <= 16 ^ 3) by (apply Z.pow_le_mono_r; lia); cbn in *; lia));
(eapply (hex4_turn W regs memc mdc STK sp0 FP ly S Hp W0 mem0 md0 own lyc Sc Hpc k p o sp ra0 i v c _
HJ Hi Hvb Hc256 R1 Hra TR Hsp16 Hsplo Hsphi Mra HPa RAp Mc HOa HOal RAo Hsp_p)).
{ intros d mem2 mdc2 regs2 Hhv Hne HK2 HG2 HJ2 TR2 HKK. exfalso. lia. }
{ intros d mem2 mdc2 regs2 Hhv Heq HK2 HG2 HJ2 R2' R11' R13' R14' HKK.
pose proof (hexval_range c d Hhv) as Hd.
assert (Hi3 : i = 3) by lia.
eapply SRr_mono.
- eapply (hex4_final W regs2 mem2 mdc2 STK sp0 FP ly S Hp W0 mem0 md0 own lyc Sc Hpc k o sp (16 * v + d) ra0 HJ2);
[ rewrite (HKK 1%bv ltac:(cbv; tauto)); exact R1 | exact Hra | exact Hra2 | exact R2' | exact R11' | exact R13' | exact R14'
| subst i; cbn in Hv; lia | exact Hsp16 | exact Hsplo | exact Hsphi | exact Hsp0a | exact Hsp0b
| exact (keeps_val_mem W memc mem2 (sp + 8) 8 ra0 HK2 ltac:(lia) ltac:(cbn; lia) Mra)
| exact HOa | exact HOal
| exact (keeps_ra W memc mem2 o 4 HK2 ltac:(lia) ltac:(unfold kLowShadowBeg, kHighMemBeg, ASAN_CEIL in *; lia) RAo)
| exact HAWR | intros x Hx; exact (apresent_grows (w_H W) memc mem2 x HG2 (HOpres x Hx))
| exact Hsp_o ].
- cbv beta. intros W' c' Hwle (-> & regs' & mem' & md' & Hc' & HJ' & HKK' & R2'' & R10' & MV & HKEEP').
split; [reflexivity|]. exists regs', mem', md'.
split; [rewrite Hc', (HKK 1%bv ltac:(cbv; tauto)); reflexivity|].
split; [exact HJ'|].
split; [intros r Hr; rewrite (HKK' r Hr); exact (HKK r Hr)|].
split; [exact R2''|].
split; [intros x Hx Hnot; rewrite (HKEEP' x Hx Hnot); exact (HK2 x Hx)|].
cbn [hacc]. rewrite Hhv.
assert (Hr0 : rest' = []) by (destruct rest' as [|y r2]; [reflexivity | cbn [length] in Hlen; exfalso; lia]).
rewrite Hr0. cbn [hacc]. split; [exact R10' | exact MV]. }
{ intros mem2 mdc2 regs2 Hhv HK2 HG2 HJ2 R2' HKK.
eapply SRr_mono.
- eapply (hex4_failret W regs2 mem2 mdc2 STK sp0 FP ly S Hp W0 mem0 md0 own lyc Sc Hpc k sp ra0 HJ2);
[ rewrite (HKK 1%bv ltac:(cbv; tauto)); exact R1 | exact Hra | exact Hra2 | exact R2'
| exact Hsp16 | exact Hsplo | exact Hsphi
| exact (keeps_val_mem W memc mem2 (sp + 8) 8 ra0 HK2 ltac:(lia) ltac:(cbn; lia) Mra) ].
- cbv beta. intros W' c' Hwle (-> & regs' & mem' & md' & Hc' & HJ' & HKK' & R2'' & R10' & HKEEP').
split; [reflexivity|]. exists regs', mem', md'.
split; [rewrite Hc', (HKK 1%bv ltac:(cbv; tauto)); reflexivity|].
split; [exact HJ'|].
split; [intros r Hr; rewrite (HKK' r Hr); exact (HKK r Hr)|].
split; [exact R2''|].
split; [intros x Hx Hnot; rewrite (HKEEP' x Hx); exact (HK2 x Hx)|].
cbn [hacc]. rewrite Hhv.
split; [exact R10' | intros x Hx; rewrite (HKEEP' x ltac:(unfold kLowShadowBeg, kHighMemBeg, ASAN_CEIL in *; lia));
exact (HK2 x ltac:(unfold kLowShadowBeg, kHighMemBeg, ASAN_CEIL in *; lia))]. }
{ intros d mem2 mdc2 regs2 Hhv Hne HK2 HG2 HJ2 TR2 HKK.
pose proof (hexval_range c d Hhv) as Hd.
eapply SRr_mono.
- eapply (IH (i + 1) (16 * v + d) W regs2 mem2 mdc2 STK sp0 FP ly S Hp W0 mem0 md0 own lyc Sc Hpc k p o sp ra0 rest');
[ lia | lia | rewrite Z.pow_add_r by lia; cbn [Z.pow Z.pow_pos Pos.iter]; lia
| exact HJ2 | rewrite (HKK 1%bv ltac:(cbv; tauto)); exact R1 | exact Hra | exact Hra2
| exact TR2 | exact Hsp16 | exact Hsplo | exact Hsphi | exact Hsp0a | exact Hsp0b
| exact (keeps_val_mem W memc mem2 (sp + 8) 8 ra0 HK2 ltac:(lia) ltac:(cbn; lia) Mra)
| exact HPa
| exact (keeps_ra W memc mem2 p 4 HK2 ltac:(lia) ltac:(unfold kLowShadowBeg, kHighMemBeg, ASAN_CEIL in *; lia) RAp)
| replace (p + (i + 1)) with (p + i + 1) by lia;
exact (keeps_garr8 W memc mem2 (p + i + 1) rest' HK2 ltac:(lia)
ltac:(unfold kLowShadowBeg, kHighMemBeg, ASAN_CEIL in *; lia) (garr8_tl W memc (p + i) c rest' GBS))
| lia | exact HOa | exact HOal
| exact (keeps_ra W memc mem2 o 4 HK2 ltac:(lia) ltac:(unfold kLowShadowBeg, kHighMemBeg, ASAN_CEIL in *; lia) RAo)
| exact HAWR | intros x Hx; exact (apresent_grows (w_H W) memc mem2 x HG2 (HOpres x Hx))
| exact Hsp_p | exact Hsp_o ].
- cbv beta. intros W' c' Hwle (-> & regs' & mem' & md' & Hc' & HJ' & HKK' & R2'' & HKEEP' & Hres).
split; [reflexivity|]. exists regs', mem', md'.
split; [rewrite Hc', (HKK 1%bv ltac:(cbv; tauto)); reflexivity|].
split; [exact HJ'|].
split; [intros r Hr; rewrite (HKK' r Hr); exact (HKK r Hr)|].
split; [exact R2''|].
split; [intros x Hx Hnot; rewrite (HKEEP' x Hx Hnot); exact (HK2 x Hx)|].
cbn [hacc]. rewrite Hhv.
destruct (hacc (16 * v + d) rest') as [h|].
+ destruct Hres as (R10' & MV). split; [exact R10' | exact MV].
+ destruct Hres as (R10' & Hk). split; [exact R10' | intros x Hx; rewrite (Hk x Hx);
exact (HK2 x ltac:(unfold kLowShadowBeg, kHighMemBeg, ASAN_CEIL in *; lia))]. }
{ intros d mem2 mdc2 regs2 Hhv Heq HK2 HG2 HJ2 R2' R11' R13' R14' HKK. exfalso. lia. }
{ intros mem2 mdc2 regs2 Hhv HK2 HG2 HJ2 R2' HKK.
eapply SRr_mono.
- eapply (hex4_failret W regs2 mem2 mdc2 STK sp0 FP ly S Hp W0 mem0 md0 own lyc Sc Hpc k sp ra0 HJ2);
[ rewrite (HKK 1%bv ltac:(cbv; tauto)); exact R1 | exact Hra | exact Hra2 | exact R2'
| exact Hsp16 | exact Hsplo | exact Hsphi
| exact (keeps_val_mem W memc mem2 (sp + 8) 8 ra0 HK2 ltac:(lia) ltac:(cbn; lia) Mra) ].
- cbv beta. intros W' c' Hwle (-> & regs' & mem' & md' & Hc' & HJ' & HKK' & R2'' & R10' & HKEEP').
split; [reflexivity|]. exists regs', mem', md'.
split; [rewrite Hc', (HKK 1%bv ltac:(cbv; tauto)); reflexivity|].
split; [exact HJ'|].
split; [intros r Hr; rewrite (HKK' r Hr); exact (HKK r Hr)|].
split; [exact R2''|].
split; [intros x Hx Hnot; rewrite (HKEEP' x Hx); exact (HK2 x Hx)|].
cbn [hacc]. rewrite Hhv.
split; [exact R10' | intros x Hx; rewrite (HKEEP' x ltac:(unfold kLowShadowBeg, kHighMemBeg, ASAN_CEIL in *; lia));
exact (HK2 x ltac:(unfold kLowShadowBeg, kHighMemBeg, ASAN_CEIL in *; lia))]. }
Qed.
Lemma ret_ok_mod2 : forall k : word, YK0s.ret_ok k -> bv_unsigned k mod 2 = 0.
Proof.
intros k H. unfold YK0s.ret_ok, v_jalr, jalr_tgtZ in H. rewrite Z.add_0_r in H.
apply (f_equal bv_unsigned) in H. rewrite Z_to_bv_unsigned in H.
assert (Hb : Z.testbit (bv_unsigned k) 0 = false).
{ rewrite <- H at 1. unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64).
rewrite Z.mod_pow2_bits_low by lia. rewrite Z.land_spec.
replace (Z.testbit (-2) 0) with false by reflexivity. apply andb_false_r. }
rewrite Z.bit0_odd in Hb. rewrite Zmod_odd, Hb. reflexivity.
Qed.
Lemma regs_pres_of_kept : forall (regs regs' : bvmap 5 word),
(forall r, In r HEX4_KEPT -> getr regs' r = getr regs r) -> getr regs' 2 = getr regs 2 ->
aregs_preserved regs regs'.
Proof.
intros regs regs' HK H2 r Hr. cbv [acallee_saved] in Hr.
assert (Hall : r = 2 \/ r = 3 \/ r = 4 \/ r = 8 \/ r = 9 \/ r = 18 \/ r = 19 \/ r = 20 \/ r = 21 \/ r = 22
\/ r = 23 \/ r = 24 \/ r = 25 \/ r = 26 \/ r = 27) by lia.
clear Hr.
repeat match goal with
| H : _ \/ _ |- _ => destruct H as [->|H];
[ first [exact H2 | apply HK; cbv [HEX4_KEPT In];
solve [repeat first [(left; apply bv_eq; vm_compute; reflexivity) | right]]] | ]
| H : r = _ |- _ => rewrite H;
first [exact H2 | apply HK; cbv [HEX4_KEPT In];
solve [repeat first [(left; apply bv_eq; vm_compute; reflexivity) | right]]]
end.
Qed.
Theorem hex4_x_holds : thex4_leafX SK rsegs B PST ARx (img_sigma AS_hex4).
Proof.
change (img_sigma AS_hex4) with HEX4_B. unfold thex4_leafX.
intros STK sp0 FP ly S Hp W0 mem0 md0 own lyc Sc Hpc W memc mdc k regs p o BS
HJ Hret Hra4 R10 R11 Hsp16 Hsp0a Hsp0b HPres HPlo HPam RAp GBS Hlen HOlo HOhi HOal RAo HOpres Hsep Hsp_p.
pose proof (proj1 (@ASAN_CEIL_range _)) as HCEIL.
assert (HPhi : p + 4 < 2 ^ 47) by (unfold amem_range, kLowMemEnd, kHighMemBeg, kHighMemEnd in HPam; lia).
assert (HPa : hex4_src_ok p)
by (split; [exact HPlo | unfold amem_range, kLowMemEnd, kHighMemBeg, kHighMemEnd in HPam; lia]).
pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hstk & _ & _).
pose proof Hstk as (Hsp016 & HSTK0 & Hceil & Hslo & Hshi & H47 & _ & _ & _).
pose proof (ret_ok_mod2 _ Hret) as Hra2.
assert (Hra64 : 4096 <= raZ regs < 2 ^ 64).
{ pose proof (bv_unsigned_in_range 64 (getr regs 1)) as Hx.
change (bv_modulus 64) with (2 ^ 64) in Hx. unfold raZ in *. lia. }
set (spE := spZ regs) in *. set (ra0 := raZ regs) in *.
assert (R1 : getr regs 1 = w64 ra0) by (unfold ra0, raZ, w64; rewrite Z_to_bv_bv_unsigned; reflexivity).
assert (R2 : getr regs 2 = w64 spE) by (unfold spE, spZ, w64; rewrite Z_to_bv_bv_unsigned; reflexivity).
assert (HspL : 2 ^ 46 <= spE - 16) by (unfold spE, HEX4_STK, ASAN_CEIL in *; lia).
assert (HspH : spE <= 2 ^ 47) by (unfold spE, HEX4_STK, ASAN_CEIL in *; lia).
assert (HOa : hex4_out_ok o) by (unfold hex4_out_ok; split; lia).
assert (HAWR : forall x, o <= x < o + 4 -> awr_byte STK sp0 FP (ablocks B ly S) (ablocks B lyc Sc) lyc own x)
by (intros x Hx; unfold awr_byte; left; unfold HEX4_STK in Hsp0a; lia).
assert (Hsp_o : spE <= o \/ o + 4 <= spE - HEX4_STK) by (left; exact HOlo).
destruct (hex4_entry_ok W regs memc mdc lyc Sc Hpc p o spE (proj1 HJ) R2 HspL HspH Hsp16
R10 R11 HPa HOa HOal RAp RAo HPres) as (HS & SHOK).
unfold cfg_at.
xrunto (HEX4_B + 0x34) HS HJ SHOK.
{ intros a (r & Hin & Hr). cbn [ss_mem ss_e In] in Hin.
destruct Hin as [<-|[<-|[<-|[]]]]; unfold stkE, gotR, cellR in Hr;
cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi base_val] in Hr;
[ | lia | lia ].
rewrite (ew_Ereg_nat regs _ 2 2%bv eq_refl), R2 in Hr. unfold w64 in Hr.
rewrite (unsigned_lit_small spE) in Hr by lia. left. unfold HEX4_STK in *. lia. }
xafter HS' HJ' SHOK'.
prreg HS' (1%bv : bv 5) P1. prreg HS' (2%bv : bv 5) P2. prreg HS' (5%bv : bv 5) P5.
prreg HS' (6%bv : bv 5) P6. prreg HS' (7%bv : bv 5) P7. prreg HS' (10%bv : bv 5) P10.
prreg HS' (11%bv : bv 5) P11. prreg HS' (12%bv : bv 5) P12. prreg HS' (13%bv : bv 5) P13.
prreg HS' (14%bv : bv 5) P14. prreg HS' (15%bv : bv 5) P15. prreg HS' (16%bv : bv 5) P16.
prreg HS' (17%bv : bv 5) P17.
assert (HAE : env_agree 32 (Ereg regs [w64 SHADOW_OFF]) (Ereg regs [w64 SHADOW_OFF])) by apply env_agree_refl.
pose proof (regs_kept_of_st_ok rsegs _ _ _ regs [w64 SHADOW_OFF] HEX4_KEPT HS'
ltac:(env_agree_chain HAE) ltac:(vm_compute; reflexivity)) as HKE.
cbn [ms_regs restrict] in HKE, P1, P2, P5, P6, P7, P10, P11, P12, P13, P14, P15, P16, P17.
pose proof (st_ok_region_nth _ _ _ 0%nat
(YP09.mkRegion (Some 2%nat) (-16) 0 (-16) 0 [YP09.mkChunk (-8) (CVal 8 (SOff 1 0))]) HS' eq_refl) as HRstk.
destruct HRstk as (_ & _ & _ & Hcs). cbn [YP09.r_base YP09.r_chunks base_val] in Hcs.
assert (HKO : keeps_out W (spE - 16) spE memc (ms_mem msx)).
{ intros x Hx Hnot. apply (frame_aview (Ereg regs [w64 SHADOW_OFF]) (ss_mem ss_e) memc _ (w_H W) x HFr Hx).
intros (r & Hin & Hr). cbn [ss_mem ss_e In] in Hin.
destruct Hin as [<-|[<-|[<-|[]]]]; unfold stkE, gotR, cellR in Hr;
cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi base_val] in Hr; [|lia|lia].
rewrite (ew_Ereg_nat regs _ 2 2%bv eq_refl), R2 in Hr. unfold w64 in Hr.
rewrite (unsigned_lit_small spE) in Hr by lia. lia. }
assert (Mra : val_mem rsegs (mrestrict (w_H W) (ms_mem msx)) (spE - 16 + 8) 8 ra0).
{ replace (spE - 16 + 8) with (spE + -8) by lia.
apply (val_of_chunk_ok rsegs (Ereg regs [w64 SHADOW_OFF]) _ spE (-8) 8 (SOff 1 0) ra0);
[ | cbn [sv_denot]; rewrite (ew_Ereg_nat regs _ 1 1%bv eq_refl), R1, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
| lia | lia].
rewrite (ew_Ereg_nat regs _ 2 2%bv eq_refl), R2 in Hcs. unfold w64 in Hcs.
rewrite (unsigned_lit_small spE) in Hcs by lia.
exact (proj1 (Forall_forall _ _) Hcs _ ltac:(left; reflexivity)). }
pmkst HS'.
eapply SRr_mono.
- eapply (hex4_loop 3%nat 0 0 W (ms_regs msx) (ms_mem msx) _ STK sp0 FP ly S Hp W0 mem0 md0 own lyc Sc Hpc k
p o (spE - 16) ra0 BS);
[ cbn; reflexivity | lia | cbn; lia | exact HJ'
| rewrite P1, (ew_Ereg_nat regs _ 1 1%bv eq_refl); exact R1 | exact Hra64 | exact Hra2
| unfold turn_regs_ok; repeat split;
  [ rewrite P2, (ew_Ereg_nat regs _ 2 2%bv eq_refl), R2; unfold w64;
rewrite (unsigned_lit_small spE) by lia; f_equal; lia
  | rewrite P5; reflexivity | rewrite P6; reflexivity
  | rewrite P7, (ew_Ereg_nat regs _ 10 10%bv eq_refl), R10; unfold w64; f_equal; lia
  | rewrite P10, (ew_Ereg_nat regs _ 10 10%bv eq_refl); exact R10
  | rewrite P11, (ew_Ereg_nat regs _ 11 11%bv eq_refl); exact R11
  | rewrite P12, (ew_Ereg_nat regs _ 10 10%bv eq_refl), R10; unfold w64; f_equal; lia
  | rewrite P13; reflexivity
  | rewrite P14; cbn [ew Ereg nth Nat.ltb Nat.leb]; reflexivity
  | rewrite P15; unfold w64; f_equal; lia
  | rewrite P16; reflexivity | rewrite P17; reflexivity ]
| lia | lia | lia | unfold HEX4_STK in Hsp0a; lia | lia
| exact Mra | exact HPa
| exact (out_ra W (spE - 16) spE memc (ms_mem msx) p 4 HKO ltac:(lia)
ltac:(unfold kLowShadowBeg, kHighMemBeg, ASAN_CEIL in *; lia) ltac:(unfold SHADOW_OFF; lia) RAp)
| rewrite Z.add_0_r;
exact (out_garr8 W (spE - 16) spE memc (ms_mem msx) p BS HKO ltac:(lia)
ltac:(unfold kLowShadowBeg, kHighMemBeg, ASAN_CEIL in *; lia)
ltac:(unfold HEX4_STK in Hsp_p; lia) GBS)
| rewrite Z.sub_0_r; exact Hlen | exact HOa | exact HOal
| exact (out_ra W (spE - 16) spE memc (ms_mem msx) o 4 HKO ltac:(lia)
ltac:(unfold kLowShadowBeg, kHighMemBeg, ASAN_CEIL in *; lia) ltac:(unfold SHADOW_OFF; lia) RAo)
| exact HAWR
| intros x Hx; exact (apresent_grows (w_H W) memc (ms_mem msx) x HG (HOpres x Hx))
| unfold HEX4_STK in Hsp_p; lia | unfold HEX4_STK in Hsp_o; lia ].
- cbv beta. intros W' c' Hwle (-> & regs' & mem' & md' & Hc' & HJ2 & HKK & R2' & HKEEP & Hres).
split; [reflexivity|]. exists regs', mem', md'.
split; [rewrite Hc', P1, (ew_Ereg_nat regs _ 1 1%bv eq_refl); reflexivity|].
split; [exact HJ2|].
split.
{ apply (regs_pres_of_kept regs regs').
- intros r Hr. rewrite (HKK r Hr). exact (HKE r Hr).
- rewrite R2', R2. unfold w64. f_equal. lia. }
split.
{ intros x Hx Hn1 Hn2. unfold HEX4_STK in Hn1.
rewrite (HKEEP x Hx Hn2). exact (HKO x Hx ltac:(lia)). }
rewrite (hacc_hex4 BS Hlen) in Hres.
destruct (PjGrammar.hex4 BS) as [h|].
+ exact Hres.
+ destruct Hres as (R10' & Hk). split; [exact R10'|].
intros x Hx. rewrite (Hk x Hx).
exact (HKO x ltac:(unfold kLowShadowBeg, kHighMemBeg, ASAN_CEIL in *; lia) ltac:(unfold HEX4_STK in *; lia)).
Qed.
End a.
