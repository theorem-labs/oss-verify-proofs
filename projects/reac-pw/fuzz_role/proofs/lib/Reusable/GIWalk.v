From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Reusable Require Import
YK11 YK0o YK0s YK15 YM06 YM02 YP0m YP0e YP09 YP0l YP0k YP06 YP03 YP08 YN3v.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Reusable Require Import YO0i YO0f YO0d.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Reusable Require Import YN03 YL07 YL01 YL08 YL0d YL00 YL0g YL0i YL0k.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Reusable Require Import YM05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Open Scope Z_scope.
Definition g_img_check (G : list (Z * Z)) (rs : smem) : bool :=
forallb (fun p => img_covered rs (fst p) (snd p)) G.
Definition g_wr_region_ok (G : list (Z * Z)) (F : facts) (r : YP09.region) : bool :=
(r_whi r <=? r_wlo r) ||
match r_base r with
| None => forallb (fun p => ivl_disjoint (fst p, fst p + snd p) (r_wlo r, r_whi r)) G
| Some n => match anch_lo F n with Some K => 0 <=? K + r_wlo r | None => false end
end.
Definition g_wr_check (G : list (Z * Z)) (F : facts) (rs : smem) : bool :=
forallb (fun p => (0 <=? fst p) && (fst p + snd p <=? CEIL_MIN)) G && forallb (g_wr_region_ok G F) rs.
Definition gcarve (G : list (Z * Z)) (l : list (nat * YP09.region)) : list (nat * YP09.region) :=
fold_left (fun acc g => flat_map (split_win (fst g) (fst g + snd g)) acc) G l.
Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Lemma st_ok_G_img : forall segs E ss ms G,
st_ok segs E ss ms -> g_img_check G (ss_mem ss) = true -> G_img segs G (ms_mem ms).
Proof using.
intros segs E ss ms G HS H a (lo & len & Hp & Ha).
destruct HS as (_ & _ & _ & _ & _ & _ & _ & HM & _).
pose proof (forallb_In _ _ (lo, len) H Hp) as Hc. cbn [fst snd] in Hc.
exact (img_covered_sound segs E (ms_mem ms) (ss_mem ss) lo len HM Hc a Ha).
Qed.
Section b.
Variable G : list (Z * Z).
Lemma g_wr_check_out : forall E F rs a,
stack_anchored E F -> g_wr_check G F rs = true -> in_globals G a -> 0 <= a < 2 ^ 64 /\ ~ in_wrange E rs a.
Proof using rc.
intros E F rs a HSA H (lo & len & Hp & Ha).
apply andb_prop in H as [HG Hrs].
pose proof (forallb_In _ _ (lo, len) HG Hp) as Hp'. cbn [fst snd] in Hp'.
apply andb_prop in Hp' as [Hp0 Hp1]. apply Z.leb_le in Hp0. apply Z.leb_le in Hp1.
pose proof YM05.alloc_ceiling_val as Hcv.
split; [lia|]. intros (r & Hr & Hw).
pose proof (forallb_In _ _ r Hrs Hr) as Hr'. unfold g_wr_region_ok in Hr'.
apply orb_prop in Hr' as [Hr'|Hr']; [apply Z.leb_le in Hr'; lia|].
destruct (r_base r) as [n|] eqn:Hb; cbn [base_val] in Hw.
- destruct (anch_lo F n) as [K|] eqn:HK; [|discriminate]. apply Z.leb_le in Hr'.
pose proof (stack_anchored_sound E F n K HSA HK). lia.
- pose proof (forallb_In _ _ (lo, len) Hr' Hp) as D. unfold ivl_disjoint in D. cbn [fst snd] in D.
apply orb_prop in D as [D|D]; apply Z.leb_le in D; lia.
Qed.
End b.
Section c.
Variable B : malloc_syms.
Variable MR : MR_t.
Hypothesis LAWS : MR_laws B MR.
Hypothesis AX : AllocExtra B MR.
Variable G : list (Z * Z).
Variable GI : nat -> list (Z * Z) -> (word -> option byte) -> Prop.
Hypothesis GIL : G_local_T (ms_segs B) G GI.
Variable keep : ivl.
Lemma GI_frame_T : forall j T L A md m m' E F rs,
GI j T m -> tb_live L A T -> MR L A m md -> facts_ok E F -> stack_anchored E F ->
g_wr_check G F rs = true -> wr_check B F keep rs = true -> frame_of E rs m m' -> GI j T m'.
Proof using GIL LAWS AX rc.
intros j T L A md m m' E F rs H HTL HMR HG HSA Hck Hwk HF. apply (GIL j T m m'); [|exact H].
intros a [Ha|(t & k & Ht & Ha)].
- destruct (g_wr_check_out G E F rs a HSA Hck Ha) as [Ha64 Hn].
unfold mbyte. rewrite (HF (Z_to_bv 64 a)); [reflexivity|].
rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64). rewrite Z.mod_small by lia. exact Hn.
- destruct HTL as [_ HTL]. pose proof (HTL _ Ht) as Hb. unfold blocks in Hb.
apply in_map_iff in Hb as ((q & k') & Hq & Hin). cbn [fst snd] in Hq. injection Hq as <- <-.
replace a with (ptr_addr L q + (a - ptr_addr L q)) by lia.
exact (blk_after_frame B MR LAWS AX L A m m' md E F keep rs q k' HMR HG HSA Hwk HF Hin (a - ptr_addr L q) ltac:(lia)).
Qed.
End c.
End a.
Ltac drv_gi_T gfr E HS HF HGI HTL HMR :=
lazymatch type of HF with frame_of _ ?rs0 _ _ =>
let F := lazymatch type of HS with st_ok _ _ ?ss' _ => constr:(ss_facts ss') | st_ok_ecall _ _ ?ss' _ => constr:(ss_facts ss') end in
let HG0 := fresh "HG0" in
assert (HG0 : facts_ok E F) by (lazymatch type of HS with
| st_ok _ _ _ _ => destruct HS as (_ & _ & _ & _ & _ & _ & _ & _ & X); exact X
| st_ok_ecall _ _ _ _ => destruct HS as (_ & _ & _ & _ & _ & _ & _ & _ & X); exact X end);
let HSA0 := fresh "HSA0" in
assert (HSA0 : stack_anchored E F) by drv_anch;
let HGI' := fresh "HGI" in
pose proof (gfr _ _ _ _ _ _ _ E F rs0 HGI HTL HMR HG0 HSA0 ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) HF) as HGI';
clear HGI HG0 HSA0; rename HGI' into HGI
end.
