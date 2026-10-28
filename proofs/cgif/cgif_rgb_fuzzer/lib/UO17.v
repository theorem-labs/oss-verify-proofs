(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OssFuzzTheorems.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import
YK11 YK0i YK0j YK14 YK1b YK15 YK0o YK0v YQ0k YN06 YK0s YN02.
From OssFuzzTheorems.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import
YQ0j YQ0c YQ0b YQ03 YQ0i YQ0h YQ09 YQ04 YQ05 YQ0e.
From OssFuzzTheorems.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YP09 YP0a YP0b.
From OssFuzzTheorems.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import UH04 UH07 UH06.
From OssFuzzTheorems.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import
YP0j YP0g YP0h YP0q YP0m YP0o YP10 YP0v
YP0n YP0r YP0u YP0c.
From OssFuzzTheorems.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YO04 YO02 YO03 YQ01 YO2f
YO29 YO2a YO30 YO2z
UO0c UO08 UO0b UO16 UO0y UO0z
UO14 UO13.
From OssFuzzTheorems.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YN05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Open Scope Z_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Section f. Context {fx : YK11.FPState} {rc : YN05.RunCeil}.
Lemma chunk_bytes xv m base off (w : N) e v :
chunk_ok ubs2segs (EV xv) m base (mkChunk off (CVal w e)) ->
bv_unsigned (sv_denot (EV xv) e) = v -> 0 <= v < 2 ^ (8 * Z.of_N w) ->
bytes_at ubs2_msyms m (base + off) (N.to_nat w) v.
Proof.
intros Hc Hv Hr k Hk. destruct (Hc (Z.of_nat k) ltac:(cbn [c_len cv_len c_val]; lia)) as (b & Eb & Mb).
cbn [c_off c_val cbyte] in Eb, Mb. change (ms_segs ubs2_msyms) with ubs2segs. rewrite Mb. injection Eb as <-. f_equal.
unfold byte_of_word, le_byte. rewrite Hv, Z_to_bv8_mod. f_equal. rewrite N_nat_Z. rewrite Z.mod_small by lia. reflexivity.
Qed.

Lemma pd_app (E0 : env) l1 l2 :
pairwise_disjoint E0 l1 -> pairwise_disjoint E0 l2 ->
(forall r1 r2, In r1 l1 -> In r2 l2 -> extent_disjoint E0 r1 r2) ->
pairwise_disjoint E0 (l1 ++ l2).
Proof.
induction l1 as [|r l1 IH]; intros H1 H2 H12; cbn; [exact H2|].
destruct H1 as [Ha H1]. split.
- clear IH H1. induction l1 as [|r' l1 IH']; cbn in *.
+ clear Ha. induction l2 as [|r2 l2 IH2]; cbn; [exact I|]. split.
* apply H12; [left; reflexivity| left; reflexivity].
* apply IH2; [destruct H2; assumption|]. intros r1 r0 Hr1 Hr0. apply H12; [exact Hr1| right; exact Hr0].
+ destruct Ha as [Hrr' Ha]. split; [exact Hrr'|]. apply IH'; [exact Ha|].
intros r1 r2 Hr1 Hr2. apply H12; [destruct Hr1; [left|right;right]; assumption| exact Hr2].
- apply IH; [exact H1| exact H2|]. intros r1 r2 Hr1 Hr2. apply H12; [right; exact Hr1| exact Hr2].
Qed.
Lemma all_disjoint_app_inv (E0 : env) r l1 l2 : all_disjoint E0 r (l1 ++ l2) -> all_disjoint E0 r l1 /\ all_disjoint E0 r l2.
Proof. induction l1 as [|x l1 IH]; cbn; intros H; [split; [exact I | exact H]|]. destruct H as [H0 H]. destruct (IH H) as [H1 H2]. auto. Qed.
Lemma pd_app_inv (E0 : env) l1 l2 : pairwise_disjoint E0 (l1 ++ l2) -> pairwise_disjoint E0 l1 /\ pairwise_disjoint E0 l2.
Proof.
induction l1 as [|r l1 IH]; cbn; intros H; [split; [exact I | exact H]|].
destruct H as [Ha H]. destruct (IH H) as [H1 H2]. destruct (all_disjoint_app_inv E0 r l1 l2 Ha) as [A1 _]. auto.
Qed.
Lemma regions_wf_app l1 l2 : regions_wf (l1 ++ l2) = regions_wf l1 && regions_wf l2.
Proof. induction l1 as [|x l1 IH]; cbn; [reflexivity|]. rewrite IH, andb_assoc. reflexivity. Qed.
Lemma region_ok_ext_wf (E0 : env) m m' r :
region_wf r = true -> region_ok ubs2segs E0 m r ->
(forall x, base_val E0 (r_base r) + r_lo r <= x < base_val E0 (r_base r) + r_hi r -> m' (Z_to_bv 64 x) = m (Z_to_bv 64 x)) ->
region_ok ubs2segs E0 m' r.
Proof.
intros Hwf (R1 & R2 & R3 & R4) EQ. unfold region_wf in Hwf. apply andb_prop in Hwf as [Hwf Hci]. apply andb_prop in Hwf as [Hlh Hw].
apply Z.leb_le in Hlh.
split; [exact R1|]. split; [exact R2|]. split.
- intros o Ho. apply (writable_same2 m m'); [apply EQ | apply R3; exact Ho].
apply Bool.orb_prop in Hw. destruct Hw as [Hw|Hw]; [apply Z.leb_le in Hw; lia|]. apply andb_prop in Hw as [Hw1 Hw2]. apply Z.leb_le in Hw1. apply Z.leb_le in Hw2. lia.
- apply Forall_forall. intros c Hc i Hi. pose proof (proj1 (Forall_forall _ _) R4 c Hc i Hi) as (b & Hb1 & Hb2).
pose proof (proj1 (forallb_forall _ _) Hci c Hc) as CI. unfold chunk_inside in CI. apply andb_prop in CI as [CI CI3]. apply andb_prop in CI as [CI1 CI2].
apply Z.leb_le in CI1. apply Z.leb_le in CI2.
exists b. split; [exact Hb1|]. rewrite <- Hb2. apply same_byte_views2. apply EQ. lia.
Qed.
Definition fixed7 (stk : YQ0b.region) : smem := [reg_area; reg_ctx; reg_nl; stk; reg_got; reg_guard; reg_errnoR].
Lemma kept_of_mem_ok (E0 : env) m stk rest :
mem_ok ubs2segs E0 m ([reg_hdr0; reg_grp; reg_meta0; reg_area; reg_ctx; reg_nl; stk; reg_got; reg_guard; reg_errnoR] ++ rest) ->
Forall (region_ok ubs2segs E0 m) (fixed7 stk) /\ pairwise_disjoint E0 (fixed7 stk).
Proof.
intros (_ & ROK & PD).
change ([reg_hdr0; reg_grp; reg_meta0; reg_area; reg_ctx; reg_nl; stk; reg_got; reg_guard; reg_errnoR] ++ rest)
with ([reg_hdr0; reg_grp; reg_meta0] ++ (fixed7 stk ++ rest)) in ROK, PD.
apply Forall_app in ROK as [_ ROK]. apply Forall_app in ROK as [ROK _].
apply pd_app_inv in PD as [_ PD]. apply pd_app_inv in PD as [PD _]. split; [exact ROK | exact PD].
Qed.
Lemma fixed7_ext (E0 : env) m m' stk rest :
mem_ok ubs2segs E0 m ([reg_hdr0; reg_grp; reg_meta0; reg_area; reg_ctx; reg_nl; stk; reg_got; reg_guard; reg_errnoR] ++ rest) ->
(forall r x, In r (fixed7 stk) -> base_val E0 (r_base r) + r_lo r <= x < base_val E0 (r_base r) + r_hi r -> m' (Z_to_bv 64 x) = m (Z_to_bv 64 x)) ->
Forall (region_ok ubs2segs E0 m') (fixed7 stk).
Proof.
intros MOK EQ. pose proof MOK as (WF & _ & _). destruct (kept_of_mem_ok E0 m stk rest MOK) as [ROK _].
change ([reg_hdr0; reg_grp; reg_meta0; reg_area; reg_ctx; reg_nl; stk; reg_got; reg_guard; reg_errnoR] ++ rest)
with ([reg_hdr0; reg_grp; reg_meta0] ++ (fixed7 stk ++ rest)) in WF.
rewrite !regions_wf_app in WF. apply andb_prop in WF as [_ WF]. apply andb_prop in WF as [WF _].
apply Forall_forall. intros r Hr. apply (region_ok_ext_wf E0 m m' r).
- clear - WF Hr. unfold fixed7 in Hr. cbn [regions_wf] in WF.
repeat (apply andb_prop in WF as [?W WF]).
destruct Hr as [<-|[<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]]; assumption.
- exact (proj1 (Forall_forall _ _) ROK r Hr).
- intros x Hx. exact (EQ r x Hr Hx).
Qed.
Section h.
Variables (L : layout) (A : astate) (regs : bvmap 5 word) (mem : word -> option byte) (md : Model).
Variables (g : sptr) (am : ameta) (fr : frame) (n : Z) (a : sptr) (ka : Z) (rg : YP0j.region).
Hypothesis HC : realloc_ctx L A regs mem md g am fr n a ka rg.
Local Notation VV := (UO0y.vv L regs g am fr a rg).
Local Notation rcr := (UO0y.rcr am fr).
Let FP : free_pre K3b rcr VV mem := FP L A regs mem md g am fr n a ka rg HC.
Let PRE := rc_pre _ _ _ _ _ _ _ _ _ _ _ _ HC.
Let M : MRc ubs2_msyms L A mem md := M L A regs mem md g am fr n a ka rg HC.
Let MX : MRx ubs2_msyms L A mem md := MX L A regs mem md g am fr n a ka rg HC.
Let HW : WF A := HW L A regs mem md g am fr n a ka rg HC.
Definition MEM : Z := ptr_addr L (am_mem am).
Definition OLDLEN : Z := old_len am.
Definition NEEDED : Z := needed fr n.
Definition OFF : Z := fr_off fr.
Definition NOLD : Z := fr_n fr.
Definition G : Z := ptr_addr L g.
Definition P : Z := ptr_addr L (pp am fr).
Definition SP : Z := spZ regs.
Definition AREA : Z := ptr_addr L a.
Definition RSV' : Z := NEEDED - 20 - 16 * OFF - n.
Definition RC' : Z := if 5 <=? RSV' then 5 else RSV'.
Definition t : rcase := rcase_of RSV'.
Definition STK (x : Z) : Prop := SP - 8256 <= x < SP.
Definition ERRN (x : Z) : Prop := ERRNO2 <= x < ERRNO2 + 4.
Definition SCR (x : Z) : Prop := STK x \/ ERRN x.
Lemma ctx_lin :
0 <= OFF <= 255 /\ 131052 < NOLD /\ NOLD + 4096 <= n < 2 ^ 62 /\ n + 16 * OFF + 20 <= NEEDED /\ NEEDED < n + 16 * OFF + 20 + 4096 /\
NEEDED mod 4096 = 0 /\ 16 * OFF + NOLD + 20 <= OLDLEN /\ P = MEM + 16 + 16 * OFF /\ 4096 <= MEM /\ MEM + OLDLEN <= alloc_ceiling /\
MEM mod 4096 = 0 /\ (CEIL_MIN <= alloc_ceiling <= CEIL_MAX)   /\ alloc_ceiling + 8256 <= SP < 2 ^ 63 /\
4096 <= G /\ G + 40 <= alloc_ceiling /\ 4096 <= AREA /\ AREA + 24 <= G /\ G + 40 <= AREA + 4096 /\ AREA + 4096 <= alloc_ceiling /\
0 <= RSV' < 4096 /\ 0 <= RC' <= 5 /\ OLDLEN = am_maplen am * 4096 /\
(MEM + OLDLEN <= AREA \/ AREA + 4096 <= MEM) /\ (AREA + 4096 <= 0x10000 \/ 0x54000 <= AREA) /\ (MEM + OLDLEN <= 0x10000 \/ 0x54000 <= MEM) /\
SP mod 16 = 0.
Proof.
pose proof (rc_used _ _ _ _ _ _ _ _ _ _ _ _ HC) as Hu. pose proof (rc_fr _ _ _ _ _ _ _ _ _ _ _ _ HC) as Hfr. pose proof (rc_63 _ _ _ _ _ _ _ _ _ _ _ _ HC) as H63.
pose proof (rc_big _ _ _ _ _ _ _ _ _ _ _ _ HC) as Hbig. pose proof (rc_n _ _ _ _ _ _ _ _ _ _ _ _ HC) as Hn.
pose proof (shape ubs2_msyms L A mem md g am fr MX Hu Hfr H63) as (Hl & Hml & _ & _ & _ & _ & _ & _ & Hst & Hk & Em & Ho & Hno & Hfit).
pose proof (needed_facts' ubs2_msyms L A mem md g am fr n MX Hu Hfr H63 Hbig Hn) as (N1 & N2 & N3 & N4).
pose proof (placed ubs2_msyms L A mem md g am fr MX Hu Hfr H63) as (P1 & P2 & P3 & P4 & P5).
pose proof (lin_facts _ _ _ _ FP) as LF. cbn zeta in LF. pose proof (PRE_facts L A regs mem md g am fr n a ka rg HC) as (_ & Hal & Hceil & Hsp63 & _).
pose proof (fp_pmem _ _ _ _ FP) as PM. pose proof (off_eq L regs g am fr n a rg) as OE.
assert (EMEM : fv_mem VV = MEM) by reflexivity. assert (EG : fv_g VV = G) by reflexivity. assert (EA : fv_area VV = AREA) by reflexivity.
assert (EP : fv_p VV = P).
{ unfold fv_p. change (fv_regs VV) with regs. rewrite (rc_a0 _ _ _ _ _ _ _ _ _ _ _ _ HC). unfold P. apply lit64_small.
pose proof (mr_blocks_range _ _ (MRx_laws ubs2_msyms) L A mem md _ _ MX (rc_in _ _ _ _ _ _ _ _ _ _ _ _ HC)) as [B1 B2].
pose proof YN05.alloc_ceiling_val. unfold pp in *. clear - B1 B2 H Hbig. unfold MMAP_THRESHOLD in Hbig. lia. }
assert (EMEM' : MEM = ly_reg L (YO2z.r am)) by (unfold MEM, ptr_addr; rewrite Em; cbn; lia).
assert (EGLO : fv_glo VV = MEM) by (unfold UO0y.vv, fv_of; cbn [fv_glo]; rewrite Em; cbn [prid]; lia).
assert (EGHI : fv_ghi VV = MEM + OLDLEN).
{ unfold UO0y.vv, fv_of. cbn [fv_ghi]. destruct (reg ubs2_msyms L A mem md g am fr MX Hu Hfr H63) as (rg0 & Hr0 & _ & _ & Hlen0).
destruct (rc_rg _ _ _ _ _ _ _ _ _ _ _ _ HC) as (Hrg & _). unfold YO2z.r in Hr0, EMEM'. rewrite Hrg in Hr0. injection Hr0 as ->.
rewrite Hlen0, EMEM'. unfold OLDLEN, old_len, YO2z.OLDLEN. reflexivity. }
rewrite EMEM, EG, EA, EP, EGLO, EGHI, OE in *. fold OFF in PM.
pose proof YN05.alloc_ceiling_val as HCV.
unfold YO2z.OFF, YO2z.NOLD, YO2z.NEEDED, YO2z.OLDLEN, YO2z.MEM, YO2z.P in *.
fold MEM OFF NOLD NEEDED in Ho, Hno, Hfit, N1, N2, N3, N4, P1, P2, P3, P4, P5 |- *.
change (YO2z.G L g) with G in *. change (ptr_addr L (am_mem am)) with MEM in *. change (needed fr n) with NEEDED in *.
change (fr_off fr) with OFF in *. change (fr_n fr) with NOLD in *.
unfold RC', RSV', OLDLEN, old_len, CEIL, REALLOC_STACK, ALLOC_STACK, SP, PGSZ, MMAP_THRESHOLD in *.
rewrite <- EMEM' in P1.
repeat match goal with |- _ /\ _ => split end; try lia.
- destruct (5 <=? NEEDED - 20 - 16 * OFF - n) eqn:E5; lia.
- destruct (5 <=? NEEDED - 20 - 16 * OFF - n) eqn:E5; lia.
Qed.
Ltac ctx_tac_all :=
pose proof ctx_lin as CL;
destruct CL as (C1 & C2 & C3 & C4 & C5 & C6 & C7 & C8 & C9 & C10 & C11 & C12 & C13 & C14 & C15 & C16 & C17 & C18 & C19 & C20 & C21 & C22 & C23 & C24 & C25 & C26);
clear C6 C11 C26.
Ltac ctx_tac :=
pose proof ctx_lin as CL;
destruct CL as (C1 & C2 & C3 & C4 & C5 & C6 & C7 & C8 & C9 & C10 & C11 & C12 & C13 & C14 & C15 & C16 & C17 & C18 & C19 & C20 & C21 & C22 & C23 & C24 & C25 & C26);
clear C6 C11 C26 C23 C24 C25.
Lemma names_eq :
YO2z.MEM L am = MEM /\ YO2z.OLDLEN am = OLDLEN /\ YO2z.P L am fr = P /\
YO2z.G L g = G /\ YO2z.NEEDED fr n = NEEDED /\ YO2z.OFF fr = OFF /\ YO2z.NOLD fr = NOLD.
Proof.
pose proof (shape ubs2_msyms L A mem md g am fr MX (rc_used _ _ _ _ _ _ _ _ _ _ _ _ HC) (rc_fr _ _ _ _ _ _ _ _ _ _ _ _ HC) (rc_63 _ _ _ _ _ _ _ _ _ _ _ _ HC)) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Em & _).
pose proof ctx_lin as (_ & _ & _ & _ & _ & _ & _ & EP & _).
assert (E1 : YO2z.MEM L am = MEM) by (unfold MEM, YO2z.MEM, ptr_addr; rewrite Em; cbn; lia).
repeat split; try reflexivity.
- exact E1.
- unfold YO2z.P. rewrite E1, EP. reflexivity.
Qed.
Lemma t_cases : (RSV' = 0 /\ t = R0) \/ (1 <= RSV' <= 4 /\ t = R14) \/ (RSV' = 5 /\ t = R5) \/ (6 <= RSV' /\ t = R6).
Proof.
ctx_tac. unfold t, rcase_of.
destruct (Z.eqb_spec RSV' 0); [left; auto|]. destruct (Z.ltb_spec RSV' 5); [right; left; split; [lia|reflexivity]|].
destruct (Z.eqb_spec RSV' 5); [right; right; left; auto|]. right; right; right. split; [lia|reflexivity].
Qed.
Variables (gd err : Z).
Hypothesis Hgd : 0 <= gd < 2 ^ 64.
Hypothesis Herr : 0 <= err < 2 ^ 32.
Variable RET : Z.
Local Notation E := (Er L regs g am fr n a rg gd err).
Let XR : forall k, 0 <= xvr L regs g am fr n a rg gd err k < 2 ^ 64 :=
xvr_rangeG L A regs mem md g am fr n a ka rg HC rcr FP gd err Hgd Herr.
Definition NP : Z := RET + 16 + 16 * OFF.
Definition NEND : Z := RET + NEEDED - 4.
Definition NPN : Z := NP + n.
Hypothesis RETlo : 4096 <= RET.
Hypothesis REThi : RET + NEEDED <= alloc_ceiling.
Hypothesis RETal : RET mod 16 = 0.
Definition RET_img : Prop := RET + NEEDED <= 0x10000 \/ 0x54000 <= RET.
Definition RET_area : Prop := RET + NEEDED <= AREA \/ AREA + 4096 <= RET.
Let DEPS := conj HC (conj Hgd (conj Herr (conj RETlo (conj REThi RETal)))).
Definition xvt (k : nat) : Z :=
if (k <? 106)%nat then xvr L regs g am fr n a rg gd err k
else match k with
| 106%nat => RET
| 107%nat => NP
| 108%nat => NEND
| 109%nat => NPN
| _ => 0
end.
Definition Et : env := EV xvt.
Lemma XRt : forall k, 0 <= xvt k < 2 ^ 64.
Proof.
pose proof DEPS as DEPS'; clear DEPS'.
intros k. ctx_tac. unfold xvt. destruct (k <? 106)%nat; [apply XR|].
unfold NPN, NEND, NP in *.
do 106 (destruct k as [|k]; [lia|]). do 4 (destruct k as [|k]; [lia|]). lia.
Qed.
Lemma Et_agree : env_agree 106 E Et.
Proof.
pose proof DEPS as DEPS'; clear DEPS'.
split; [|reflexivity]. intros k Hk. unfold Et, Er, EV. cbn [ew]. unfold xvt.
replace (k <? 106)%nat with true by (symmetry; apply Nat.ltb_lt; exact Hk). reflexivity.
Qed.
Lemma xvt_lo k : (k < 106)%nat -> xvt k = xvr L regs g am fr n a rg gd err k.
Proof.
pose proof DEPS as DEPS'; clear DEPS'. intros Hk. unfold xvt. replace (k <? 106)%nat with true by (symmetry; apply Nat.ltb_lt; exact Hk). reflexivity. Qed.
Lemma vals :
xvt aRET = RET /\ xvt aNP = NP /\ xvt aNEND = NEND /\ xvt aNPN = NPN /\
xvt aMEM = MEM /\ xvt aG = G /\ xvt aP = P /\ xvt aN = n /\ xvt aB16 = 16 * OFF /\ xvt aNEED = NEEDED /\ xvt aSP = SP /\
xvt aTP = ubs2_tp /\ xvt aOFF = OFF /\ xvt aIDX = 0 /\ xvt aAV = am_avail am /\ xvt aFR = am_freed am /\ xvt aBITS = meta_bits am /\
xvt aH3 = hdr_byte3 am 0 fr /\ xvt aAREA = AREA /\ xvt aMP = OLDLEN /\ xvt 1%nat = bv_unsigned (getr regs 1).
Proof.
pose proof DEPS as DEPS'; clear DEPS'.
pose proof ctx_lin as CL.
repeat match goal with |- _ /\ _ => split end; try reflexivity; rewrite xvt_lo by (cbv; lia); unfold xvr; cbn [Nat.ltb Nat.leb].
- change (xvf VV aP) with (fv_p VV). unfold fv_p. change (fv_regs VV) with regs. rewrite (rc_a0 _ _ _ _ _ _ _ _ _ _ _ _ HC). unfold P. apply lit64_small. unfold P in CL. lia.
- exact (n_eq L A regs mem md g am fr n a ka rg HC).
- exact (xvf4 L A regs mem md g am fr n a ka rg HC).
- exact (off_eq L regs g am fr n a rg).
- cbn. unfold OLDLEN, old_len. lia.
Qed.
Ltac vals_tac :=
pose proof vals as (VRET & VNP & VNEND & VNPN & VMEM & VG & VP & VN & VB16 & VNEED & VSP & VTP & VOFF & VIDX & VAV & VFR & VBITS & VH3 & VAREA & VMP & V1).
Lemma denT k : sv_denot Et (SOff k 0) = Z_to_bv 64 (xvt k).
Proof.
pose proof DEPS as DEPS'; clear DEPS'. exact (den_off0 _ XRt k). Qed.
Lemma baseT k : base_val Et (Some k) = xvt k.
Proof.
pose proof DEPS as DEPS'; clear DEPS'. exact (base_val_EV _ XRt k). Qed.
Lemma ewT k : bv_unsigned (ew Et k) = xvt k.
Proof.
pose proof DEPS as DEPS'; clear DEPS'. exact (ew_EV _ XRt k). Qed.
Lemma WRSV_val : bv_unsigned (sv_denot Et WRSV) = RSV'.
Proof.
pose proof DEPS as DEPS'; clear DEPS'.
vals_tac. ctx_tac. unfold WRSV. cbn [sv_denot]. rewrite subw_rr_unsigned, !ewT, !Z.add_0_r, VNEND, VNPN.
unfold NPN, NEND, NP in *. rewrite !lit64_small by lia. rewrite subw_small by lia. unfold RSV'. lia.
Qed.
Lemma atoms_t : atoms_ok Et (t_atoms t).
Proof.
pose proof DEPS as DEPS'; clear DEPS'.
vals_tac. ctx_tac.
assert (A1 : afact_ok Et aNP (mkAF 4096 CEIL_MAX 4)).
{ unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite ewT, VNP. unfold NP, CEIL in *. change (2 ^ 4) with 16.
split; [lia|]. split; [|lia]. replace (RET + 16 + 16 * OFF) with (RET + (1 + OFF) * 16) by lia. rewrite Z.add_mod, RETal, Z_mod_mult by lia. reflexivity. }
assert (A2 : afact_ok Et aNEND (mkAF 4096 CEIL_MAX 0)).
{ unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite ewT, VNEND. unfold NEND, CEIL in *. change (2 ^ 0) with 1. rewrite Z.mod_1_r. lia. }
assert (A3 : afact_ok Et aNPN (mkAF 4096 CEIL_MAX 0)).
{ unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite ewT, VNPN. unfold NPN, NP, CEIL in *. change (2 ^ 0) with 1. rewrite Z.mod_1_r. lia. }
destruct t_cases as [[_ ->]|[[_ ->]|[[_ ->]|[_ ->]]]]; cbn [t_atoms atoms_ok]; auto.
Qed.
Lemma atom_RET : RET mod 4096 = 0 -> afact_ok Et aRET (mkAF 4096 CEIL_MAX 12).
Proof.
pose proof DEPS as DEPS'; clear DEPS'.
intros Hal. vals_tac. ctx_tac. unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite ewT, VRET. unfold CEIL in *. change (2 ^ 12) with 4096. lia.
Qed.
Lemma conds_t : conds_ok Et (t_conds t).
Proof.
pose proof DEPS as DEPS'; clear DEPS'.
ctx_tac. pose proof WRSV_val as W.
assert (NE : RSV' <> 0 -> acond_ok Et (mkAC BC_NE WRSV (SLit 0))).
{ intros H. unfold acond_ok. cbn [ac_c ac_a ac_b]. rewrite branch_ne, W. cbn [sv_denot]. rewrite lit64_small by lia. apply Bool.negb_true_iff. apply Z.eqb_neq. exact H. }
assert (LT : RSV' < 5 -> acond_ok Et (mkAC BC_LT WRSV (SLit 5))).
{ intros H. unfold acond_ok. cbn [ac_c ac_a ac_b]. rewrite branch_lt, W. cbn [sv_denot]. rewrite lit64_small by lia. unfold s64.
destruct (Z.ltb_spec RSV' (2 ^ 63)); [|lia]. replace (if 5 <? 2 ^ 63 then 5 else 5 - 2 ^ 64) with 5 by reflexivity. apply Z.ltb_lt. lia. }
assert (GE : 5 <= RSV' -> acond_ok Et (mkAC BC_GE WRSV (SLit 5))).
{ intros H. unfold acond_ok. cbn [ac_c ac_a ac_b]. rewrite branch_ge, W. cbn [sv_denot]. rewrite lit64_small by lia. unfold s64.
destruct (Z.ltb_spec RSV' (2 ^ 63)); [|lia]. replace (if 5 <? 2 ^ 63 then 5 else 5 - 2 ^ 64) with 5 by reflexivity. apply Bool.negb_true_iff. apply Z.ltb_ge. lia. }
destruct t_cases as [[? ->]|[[? ->]|[[? ->]|[? ->]]]]; cbn [t_conds conds_ok]; repeat split; try exact I; first [apply NE | apply LT | apply GE]; lia.
Qed.
Lemma alias_t base : xvt base = RET -> alias_ok Et (t_alias base t).
Proof.
pose proof DEPS as DEPS'; clear DEPS'.
intros Hb. vals_tac. ctx_tac. pose proof WRSV_val as W.
assert (X1 : sv_denot Et (SAlu ALU_ADD (SOff base 0) (SOff aB16 0)) = sv_denot Et (SOff aNP (-16))).
{ apply (proj2 (word_eq _ _)). cbn [sv_denot]. rewrite alu64_add, !ewT, !Z.add_0_r, Hb, VB16, VNP. rewrite !lit64_small by (unfold NP in *; lia). unfold add64, NP. rewrite Z.mod_small by lia. lia. }
assert (X2 : sv_denot Et (SAlu ALU_ADD (SOff base 0) (SOff aNEED 0)) = sv_denot Et (SOff aNEND 4)).
{ apply (proj2 (word_eq _ _)). cbn [sv_denot]. rewrite alu64_add, !ewT, !Z.add_0_r, Hb, VNEED, VNEND. rewrite !lit64_small by (unfold NEND in *; lia). unfold add64, NEND. rewrite Z.mod_small by lia. lia. }
assert (X3 : forall d, NP + n = NEND + d -> sv_denot Et (SAlu ALU_ADD (SOff aN 0) (SOff aNP 0)) = sv_denot Et (SOff aNEND d)).
{ intros d Hd. apply (proj2 (word_eq _ _)). cbn [sv_denot]. rewrite alu64_add, !ewT, !Z.add_0_r, VN, VNP, VNEND. rewrite !lit64_small by (unfold NEND, NP in *; lia). unfold add64. rewrite Z.mod_small by (unfold NP, NEND in *; lia). lia. }
assert (X4 : sv_denot Et (SAlu ALU_ADD (SOff aN 0) (SOff aNP 0)) = sv_denot Et (SOff aNPN 0)).
{ apply (proj2 (word_eq _ _)). cbn [sv_denot]. rewrite alu64_add, !ewT, !Z.add_0_r, VN, VNP, VNPN. rewrite !lit64_small by (unfold NPN, NP in *; lia). unfold add64, NPN. rewrite Z.mod_small by (unfold NP in *; lia). lia. }
assert (X5 : 0 < RSV' -> sv_denot Et (SAlu ALU_ADD (SOff aNEND 0) (SAluw ALU_SUB (SLit 0) WRSV)) = sv_denot Et (SOff aNPN 0)).
{ intros H. apply (proj2 (word_eq _ _)). cbn [sv_denot]. rewrite alu64_add. rewrite negw_unsigned. fold (sv_denot Et WRSV).
change (sext 64 (alu32 ALU_SUB (low32 (sv_denot Et (SOff aNEND 0))) (low32 (sv_denot Et (SOff aNPN 0))))) with (sv_denot Et WRSV). rewrite W.
rewrite !ewT, !Z.add_0_r, VNEND, VNPN. rewrite !lit64_small by (unfold NPN, NP, NEND in *; lia). unfold negw. rewrite sx32_neg_small by lia.
unfold add64, NPN, NP, NEND, RSV' in *. rewrite <- Z.add_mod_idemp_r by lia.
replace (2 ^ 64 - (NEEDED - 20 - 16 * OFF - n)) with ((2 ^ 64 - (NEEDED - 20 - 16 * OFF - n))) by lia.
rewrite (Z.add_mod_idemp_r) by lia. replace (RET + NEEDED - 4 + (2 ^ 64 - (NEEDED - 20 - 16 * OFF - n))) with ((RET + 16 + 16 * OFF + n) + 1 * 2 ^ 64) by lia.
rewrite Z_mod_plus_full. apply Z.mod_small. lia. }
destruct t_cases as [[R ->]|[[R ->]|[[R ->]|[R ->]]]]; cbn [t_alias alias_ok]; repeat split; try exact I; try assumption.
- apply X3. unfold NP, NEND, RSV' in *. lia.
- apply X5. lia.
- apply X3. unfold NP, NEND, RSV' in *. lia.
- apply X5. lia.
Qed.
Lemma facts_ok_app G0 ats cnds als :
facts_ok Et G0 -> atoms_ok Et ats -> conds_ok Et cnds -> alias_ok Et als -> facts_ok Et (facts_app G0 ats cnds als).
Proof.
pose proof DEPS as DEPS'; clear DEPS'.
intros (F1 & F2 & F3) H1 H2 H3. unfold facts_app. split; [|split]; cbn [f_atoms f_conds f_alias].
- apply atoms_ok_app; assumption.
- apply conds_ok_app; assumption.
- apply alias_ok_app; assumption.
Qed.
Definition tail_regs (stk : YQ0b.region) : smem :=
[reg_area; reg_ctx; reg_nl; stk; reg_got; reg_guard; reg_errnoR; reg_metaR; reg_nhdr] ++ t_mem t.
Lemma tail_mem_S1 : tail_mem (S1 rcr) t = tail_regs stk1.
Proof. unfold tail_regs. generalize t. clear. intros t0. unfold UO0y.rcr. destruct (rcase_of (reserved_of am fr)); vm_compute; reflexivity. Qed.
Lemma tail_mem_S2 : tail_mem (S2 rcr) t = tail_regs (stk2 rcr).
Proof. unfold tail_regs. generalize t. clear. intros t0. unfold UO0y.rcr. destruct (rcase_of (reserved_of am fr)); vm_compute; reflexivity. Qed.
Lemma off_img_writable_present m x : 0 <= x < 2 ^ 64 -> (x + 1 <= 0x10000 \/ 0x54000 <= x) -> writable_at ubs2segs m x -> present m x.
Proof.
pose proof DEPS as DEPS'; clear DEPS'. intros Hx Hi W. apply (writable_off_img_present2 m x Hx); [unfold in_img1; lia | exact W]. Qed.
Section j.
Variable memc : word -> option byte.
Hypothesis MG : forall i, 0 <= i < 40 -> memc (Z_to_bv 64 (G + i)) = mem (Z_to_bv 64 (G + i)).
Hypothesis MH : forall i, 0 <= i < 4 -> memc (Z_to_bv 64 (NP - 4 + i)) = mem (Z_to_bv 64 (P - 4 + i)).
Hypothesis WN : forall x, RET <= x < RET + NEEDED -> writable_at ubs2segs memc x.
Let MDEPS := conj MG (conj MH WN).
Lemma rok_metaR : region_ok ubs2segs Et memc reg_metaR.
Proof.
pose proof DEPS as DEPS'; clear DEPS'. pose proof MDEPS as MDEPS'; clear MDEPS'.
vals_tac. ctx_tac.
pose proof (meta_writable L A regs mem md g am fr n a ka rg HC) as MW. change (fv_g VV) with G in MW.
assert (KB : forall a0 w v, G + 16 <= a0 -> a0 + Z.of_nat w <= G + 40 -> bytes_are mem a0 w v -> bytes_are memc a0 w v).
{ intros a0 w v H1 H2 Hb k Hk. rewrite <- (Hb k Hk). apply same_byte_views2. replace (a0 + Z.of_nat k) with (G + (a0 + Z.of_nat k - G)) by lia. apply MG. lia. }
apply region_ok_intro; cbn [r_base r_lo r_hi r_wlo r_whi r_chunks reg_metaR]; rewrite ?baseT, ?VG; [lia | lia | |].
- intros o Ho. apply (writable_same2 mem memc); [replace (G + o) with (G + o) by lia; apply MG; lia | apply MW; lia].
- repeat (apply Forall_cons || apply Forall_nil); eapply chunk_ok_val; rewrite ?(U_off0 _ XRt), ?VMEM, ?VAV, ?VFR, ?VBITS; try reflexivity.
+ unfold MEM in *. lia.
+ apply KB; [lia | cbn; lia |]. pose proof (fp_c_g16 _ _ _ _ FP) as X. exact X.
+ pose proof (fp_vals _ _ _ _ FP) as V. cbn in V |- *. lia.
+ apply KB; [lia | cbn; lia |]. exact (fp_c_g24 _ _ _ _ FP).
+ pose proof (fp_vals _ _ _ _ FP) as V. cbn in V |- *. lia.
+ apply KB; [lia | cbn; lia |]. exact (fp_c_g28 _ _ _ _ FP).
+ pose proof (fp_vals _ _ _ _ FP) as V. cbn in V |- *. lia.
+ apply KB; [lia | cbn; lia |]. exact (fp_c_g32 _ _ _ _ FP).
Qed.
Lemma rok_nhdr : region_ok ubs2segs Et memc reg_nhdr.
Proof.
pose proof DEPS as DEPS'; clear DEPS'. pose proof MDEPS as MDEPS'; clear MDEPS'.
vals_tac. ctx_tac.
pose proof (placed ubs2_msyms L A mem md g am fr MX (rc_used _ _ _ _ _ _ _ _ _ _ _ _ HC) (rc_fr _ _ _ _ _ _ _ _ _ _ _ _ HC) (rc_63 _ _ _ _ _ _ _ _ _ _ _ _ HC)) as (_ & _ & _ & PI & _).
pose proof names_eq as (NM & NO & NP' & NG & NN & NOF & NNO).
assert (OP : forall i, 0 <= i < 4 -> present mem (P - 4 + i)).
{ intros i Hi. eapply old_present; [exact MX | exact (rc_used _ _ _ _ _ _ _ _ _ _ _ _ HC) | exact (rc_fr _ _ _ _ _ _ _ _ _ _ _ _ HC) | exact (rc_63 _ _ _ _ _ _ _ _ _ _ _ _ HC) |].
rewrite NM, NO. lia. }
assert (KB : forall i w v, 0 <= i -> i + Z.of_nat w <= 4 -> bytes_are mem (P - 4 + i) w v -> bytes_are memc (NP - 4 + i) w v).
{ intros i w v H1 H2 Hb k Hk. pose proof (Hb k Hk) as B. destruct (OP (i + Z.of_nat k) ltac:(lia)) as [b Pb].
unfold mbyte in B |- *. replace (P - 4 + (i + Z.of_nat k)) with (P - 4 + i + Z.of_nat k) in Pb by lia. rewrite Pb in B.
replace (NP - 4 + i + Z.of_nat k) with (NP - 4 + (i + Z.of_nat k)) by lia. rewrite (MH (i + Z.of_nat k)) by lia.
replace (P - 4 + (i + Z.of_nat k)) with (P - 4 + i + Z.of_nat k) by lia. rewrite Pb. exact B. }
pose proof (fp_c_p4 _ _ _ _ FP) as HB4. pose proof (fp_c_p3 _ _ _ _ FP) as HB3. pose proof (fp_c_p2 _ _ _ _ FP) as HB2.
change (fv_p VV) with (xvf VV aP) in HB4, HB3, HB2. rewrite <- (xvt_lo aP ltac:(cbv; lia)) in HB4, HB3, HB2 |- * || idtac.
assert (EPP : xvf VV aP = P) by (rewrite <- VP; rewrite xvt_lo by (cbv; lia); reflexivity). rewrite EPP in HB4, HB3, HB2.
apply region_ok_intro; cbn [r_base r_lo r_hi r_wlo r_whi r_chunks reg_nhdr]; rewrite ?baseT, ?VNP; [unfold NP in *; lia | unfold NP in *; lia | |].
- intros o Ho. apply WN. unfold NP in *. lia.
- repeat (apply Forall_cons || apply Forall_nil).
+ apply chunk_ok_lit0. intros k Hk. pose proof (KB 0 1%nat 0 ltac:(lia) ltac:(cbn; lia) ltac:(rewrite Z.add_0_r; exact HB4) k Hk) as B. rewrite le_byte_0 in B. rewrite <- B. f_equal. lia.
+ eapply chunk_ok_val; [rewrite (U_off0 _ XRt), VH3; reflexivity | pose proof (fp_vals _ _ _ _ FP) as V; cbn in V |- *; lia |].
eapply bytes_are_at; [apply (KB 1 1%nat); [lia | cbn; lia |]; replace (P - 4 + 1) with (P - 3) by lia; exact HB3 | lia].
+ eapply chunk_ok_val; [rewrite (U_off0 _ XRt), VOFF; reflexivity | cbn; lia |].
pose proof (off_eq L regs g am fr n a rg) as OE.
eapply bytes_are_at; [apply (KB 2 2%nat); [lia | cbn; lia |]; replace (P - 4 + 2) with (P - 2) by lia; unfold OFF; rewrite <- OE; exact HB2 | lia].
Qed.
Lemma rok_tmem : Forall (region_ok ubs2segs Et memc) (t_mem t).
Proof.
pose proof DEPS as DEPS'; clear DEPS'. pose proof MDEPS as MDEPS'; clear MDEPS'.
vals_tac. ctx_tac.
assert (R1 : region_ok ubs2segs Et memc reg_nend1).
{ apply region_ok_intro; cbn [r_base r_lo r_hi r_wlo r_whi r_chunks reg_nend1]; rewrite ?baseT, ?VNEND; unfold NEND in *; [lia | lia | | apply Forall_nil].
intros o Ho. apply WN. lia. }
assert (R5 : region_ok ubs2segs Et memc reg_nend5).
{ apply region_ok_intro; cbn [r_base r_lo r_hi r_wlo r_whi r_chunks reg_nend5]; rewrite ?baseT, ?VNEND; unfold NEND in *; [lia | lia | | apply Forall_nil].
intros o Ho. apply WN. lia. }
assert (RP : region_ok ubs2segs Et memc reg_npn).
{ apply region_ok_intro; cbn [r_base r_lo r_hi r_wlo r_whi r_chunks reg_npn]; rewrite ?baseT, ?VNPN; unfold NPN, NP, RSV' in *; [lia | lia | | apply Forall_nil].
intros o Ho. apply WN. lia. }
destruct t_cases as [[? ->]|[[? ->]|[[? ->]|[? ->]]]]; cbn [t_mem]; repeat (apply Forall_cons || apply Forall_nil); assumption.
Qed.
Ltac numT :=
unfold extent_disjoint; cbn [r_base r_lo r_hi r_wlo r_whi r_chunks reg_area reg_ctx reg_nl stk1 stk2 reg_got reg_guard reg_errnoR reg_metaR reg_nhdr reg_nend1 reg_nend5 reg_npn].
Ltac lits := unfold ubs2_D_malloc_context, ubs2_D_libc, ubs2_D_got_stack_chk_guard, ubs2_D_stack_chk_guard, ubs2_tp.
Lemma cross_meta stk r1 : r_base stk = Some aSP -> r_lo stk = -8256 -> r_hi stk = 0 ->
In r1 (fixed7 stk) -> extent_disjoint Et r1 reg_metaR.
Proof.
pose proof DEPS as DEPS'; clear DEPS'. pose proof MDEPS as MDEPS'; clear MDEPS'.
intros B1 B2 B3 Hin. vals_tac. ctx_tac_all. clear C23 C25. pose proof baseT as BT. pose proof ewT as ET.
clearbody FP PRE M MX HW XR. clear XR HW MX M PRE FP.
clear VRET VMEM VP VN VB16 VNEED VOFF VIDX VAV VFR VBITS VH3 VMP V1 VNP VNEND VNPN.
destruct Hin as [<-|[<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]]; numT; rewrite ?B1, ?B2, ?B3; cbn [base_val]; rewrite ?BT, ?ET, ?VAREA, ?VSP, ?VTP, ?VG;
clear BT ET; lits; lia.
Qed.
Lemma cross_new stk r1 lo2 hi2 (RETimg : RET_img) (RETarea : RET_area) : r_base stk = Some aSP -> r_lo stk = -8256 -> r_hi stk = 0 ->
In r1 (fixed7 stk) -> RET <= lo2 -> hi2 <= RET + NEEDED ->
base_val Et (r_base r1) + r_hi r1 <= lo2 \/ hi2 <= base_val Et (r_base r1) + r_lo r1.
Proof.
pose proof DEPS as DEPS'; clear DEPS'. pose proof MDEPS as MDEPS'; clear MDEPS'.
intros B1 B2 B3 Hin L2 H2. unfold RET_img in RETimg. unfold RET_area in RETarea. vals_tac. ctx_tac. pose proof baseT as BT. pose proof ewT as ET.
clearbody FP PRE M MX HW XR. clear XR HW MX M PRE FP.
clear VRET VMEM VP VN VB16 VNEED VOFF VIDX VAV VFR VBITS VH3 VMP V1 VNP VNEND VNPN.
destruct Hin as [<-|[<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]];
cbn [r_base r_lo r_hi reg_area reg_ctx reg_nl reg_got reg_guard reg_errnoR]; rewrite ?B1, ?B2, ?B3; cbn [base_val]; rewrite ?BT, ?ET, ?VAREA, ?VSP, ?VTP;
clear BT ET; lits.
- clear RETimg. lia.
- clear RETarea. lia.
- clear RETarea. lia.
- clear RETimg RETarea. lia.
- clear RETarea. lia.
- clear RETarea. lia.
- clear RETarea. lia.
Qed.
Lemma new_in_range r2 : r2 = reg_nhdr \/ r2 = reg_nend1 \/ r2 = reg_nend5 \/ r2 = reg_npn ->
RET <= base_val Et (r_base r2) + r_lo r2 /\ base_val Et (r_base r2) + r_hi r2 <= RET + NEEDED.
Proof.
pose proof DEPS as DEPS'; clear DEPS'. pose proof MDEPS as MDEPS'; clear MDEPS'.
intros Hr2. vals_tac. ctx_tac. pose proof baseT as BT.
clearbody FP PRE M MX HW XR. clear XR HW MX M PRE FP.
unfold NPN, NEND, NP in *.
destruct Hr2 as [-> | [-> | [-> | ->]]]; cbn [r_base r_lo r_hi reg_nhdr reg_nend1 reg_nend5 reg_npn]; rewrite BT, ?VNP, ?VNEND, ?VNPN; clear BT; lia.
Qed.
Lemma in_new r2 : In r2 (reg_nhdr :: t_mem t) -> r2 = reg_nhdr \/ r2 = reg_nend1 \/ r2 = reg_nend5 \/ r2 = reg_npn.
Proof.
pose proof DEPS as DEPS'; clear DEPS'. pose proof MDEPS as MDEPS'; clear MDEPS'.
intros [<-|Hin]; [left; reflexivity | right].
destruct t_cases as [[_ X]|[[_ X]|[[_ X]|[_ X]]]]; rewrite X in Hin; cbn [t_mem In] in Hin.
- destruct Hin as [<-|[]]. left; reflexivity.
- destruct Hin as [<-|[<-|[]]]; [left; reflexivity | right; right; reflexivity].
- destruct Hin as [<-|[]]. right; left; reflexivity.
- destruct Hin as [<-|[<-|[]]]; [right; left; reflexivity | right; right; reflexivity].
Qed.
Lemma pd_new (RETarea : RET_area) : pairwise_disjoint Et ([reg_metaR; reg_nhdr] ++ t_mem t).
Proof.
pose proof DEPS as DEPS'; clear DEPS'. pose proof MDEPS as MDEPS'; clear MDEPS'. unfold RET_area in RETarea.
vals_tac. ctx_tac. pose proof t_cases as TC. pose proof baseT as BT. pose proof ewT as ET. pose proof new_in_range as NR.
clearbody FP PRE M MX HW XR. clear XR HW MX M PRE FP.
assert (MR2 : forall r2, RET <= base_val Et (r_base r2) + r_lo r2 /\ base_val Et (r_base r2) + r_hi r2 <= RET + NEEDED ->
extent_disjoint Et reg_metaR r2).
{ intros r2 [L2 H2]. unfold extent_disjoint. revert L2 H2.
generalize (base_val Et (r_base r2) + r_lo r2) as lo2. generalize (base_val Et (r_base r2) + r_hi r2) as hi2. intros hi2 lo2 L2 H2.
cbn [r_base r_lo r_hi reg_metaR]. rewrite BT, VG. clear - L2 H2 RETarea C17 C18. lia. }
clear RETarea. clear VRET VMEM VP VN VB16 VNEED VOFF VIDX VAV VFR VBITS VH3 VMP V1.
unfold NPN, NEND, NP, RSV' in *.
destruct TC as [[R ->]|[[R ->]|[[R ->]|[R ->]]]]; cbn [t_mem app pairwise_disjoint all_disjoint];
repeat match goal with |- _ /\ _ => split | |- True => exact I end;
first [ apply MR2; apply NR; first [left; reflexivity | right; left; reflexivity | right; right; left; reflexivity | right; right; right; reflexivity]
| clear MR2 NR; numT; cbn [base_val]; rewrite ?BT, ?ET, ?VNP, ?VNEND, ?VNPN; clear BT ET; lia ].
Qed.
Lemma pd_tail stk (RETimg : RET_img) (RETarea : RET_area) : r_base stk = Some aSP -> r_lo stk = -8256 -> r_hi stk = 0 -> region_atoms_lt 106 stk = true ->
pairwise_disjoint E (fixed7 stk) -> pairwise_disjoint Et (tail_regs stk).
Proof.
pose proof DEPS as DEPS'; clear DEPS'. pose proof MDEPS as MDEPS'; clear MDEPS'.
intros B1 B2 B3 AT PD. unfold tail_regs.
change ([reg_area; reg_ctx; reg_nl; stk; reg_got; reg_guard; reg_errnoR; reg_metaR; reg_nhdr] ++ t_mem t)
with (fixed7 stk ++ ([reg_metaR; reg_nhdr] ++ t_mem t)).
apply pd_app.
- apply (pairwise_disjoint_agree 106 E Et _ Et_agree); [| exact PD].
unfold fixed7, mem_atoms_lt. cbn [forallb]. rewrite AT. reflexivity.
- apply pd_new. exact RETarea.
- intros r1 r2 H1 [<-|H2]; [apply (cross_meta stk); assumption|].
destruct (new_in_range r2 (in_new r2 H2)) as [L2 R2]. unfold extent_disjoint. apply (cross_new stk); assumption.
Qed.
Lemma mem_ok_tail stk (RETimg : RET_img) (RETarea : RET_area) :
r_base stk = Some aSP -> r_lo stk = -8256 -> r_hi stk = 0 -> region_atoms_lt 106 stk = true ->
regions_wf (tail_regs stk) = true ->
Forall (region_ok ubs2segs E memc) (fixed7 stk) -> pairwise_disjoint E (fixed7 stk) ->
mem_ok ubs2segs Et memc (tail_regs stk).
Proof.
pose proof DEPS as DEPS'; clear DEPS'. pose proof MDEPS as MDEPS'; clear MDEPS'.
intros B1 B2 B3 AT WF KEPT PD. split; [exact WF|]. split; [| apply pd_tail; assumption].
unfold tail_regs. change ([reg_area; reg_ctx; reg_nl; stk; reg_got; reg_guard; reg_errnoR; reg_metaR; reg_nhdr] ++ t_mem t)
with ([reg_area; reg_ctx; reg_nl; stk; reg_got; reg_guard; reg_errnoR] ++ ([reg_metaR; reg_nhdr] ++ t_mem t)).
apply Forall_app. split.
- apply Forall_forall. intros x Hx. apply (region_ok_agree ubs2segs 106 E Et memc x Et_agree); [| exact (proj1 (Forall_forall _ _) KEPT x Hx)].
destruct Hx as [<-|[<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]]; try reflexivity. exact AT.
- apply Forall_app. split; [| apply rok_tmem]. apply Forall_cons; [apply rok_metaR|]. apply Forall_cons; [apply rok_nhdr | apply Forall_nil].
Qed.
End j.
Lemma wf_tail stk : regions_wf [reg_area; reg_ctx; reg_nl; stk; reg_got; reg_guard; reg_errnoR; reg_metaR; reg_nhdr] = true ->
regions_wf (tail_regs stk) = true.
Proof.
pose proof DEPS as DEPS'; clear DEPS'.
intros H. unfold tail_regs. rewrite regions_wf_app, H. cbn [andb].
destruct t_cases as [[_ ->]|[[_ ->]|[[_ ->]|[_ ->]]]]; vm_compute; reflexivity.
Qed.
Lemma wr_tail stk x : r_base stk = Some aSP -> r_wlo stk = -8256 -> r_whi stk = 0 ->
in_wrange Et (tail_regs stk) x ->
STK x \/ ERRN x \/ (G + 16 <= x < G + 40) \/ (NP - 4 <= x < NP) \/
(0 < RSV' /\ x = NPN) \/ (5 <= RSV' /\ NEND - 5 <= x <= NEND) \/ x = NEND.
Proof.
pose proof DEPS as DEPS'; clear DEPS'.
intros B1 B2 B3 (r0 & Hin & Hx). vals_tac. ctx_tac. unfold tail_regs in Hin. apply in_app_iff in Hin as [Hin|Hin].
- destruct Hin as [<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]]]];
cbn [r_base r_wlo r_whi reg_area reg_ctx reg_nl reg_got reg_guard reg_errnoR reg_metaR reg_nhdr] in Hx; rewrite ?B1, ?B2, ?B3 in Hx; cbn [base_val] in Hx;
rewrite ?ewT, ?VAREA, ?VSP, ?VTP, ?VG, ?VNP in Hx.
+ exfalso. clear - Hx. lia.
+ exfalso. clear - Hx. lia.
+ exfalso. clear - Hx. lia.
+ left. unfold STK. clear - Hx. lia.
+ exfalso. clear - Hx. lia.
+ exfalso. clear - Hx. lia.
+ right; left. unfold ERRN. rewrite ERRNO2_val. clear - Hx. lia.
+ right; right; left. clear - Hx. lia.
+ right; right; right; left. clear - Hx. lia.
- unfold NPN, NEND, NP in *.
destruct t_cases as [[R X]|[[R X]|[[R X]|[R X]]]]; rewrite X in Hin; cbn [t_mem] in Hin;
[destruct Hin as [<-|[]] | destruct Hin as [<-|[<-|[]]] | destruct Hin as [<-|[]] | destruct Hin as [<-|[<-|[]]]];
cbn [r_base r_wlo r_whi reg_nend1 reg_nend5 reg_npn] in Hx; cbn [base_val] in Hx; rewrite ?ewT, ?VNEND, ?VNPN in Hx.
+ do 6 right. clear - Hx. lia.
+ do 6 right. clear - Hx. lia.
+ do 4 right; left. clear - Hx R. lia.
+ do 5 right; left. clear - Hx R. lia.
+ do 5 right; left. clear - Hx R. lia.
+ do 4 right; left. clear - Hx R. lia.
Qed.
Lemma new_off_img x (RETimg : RET_img) : RET <= x < RET + NEEDED -> x + 1 <= 0x10000 \/ 0x54000 <= x.
Proof. pose proof DEPS as DEPS'; clear DEPS'. unfold RET_img in RETimg. intros Hx. clear - Hx RETimg. lia. Qed.
Lemma meta_off_img x : G + 16 <= x < G + 40 -> x + 1 <= 0x10000 \/ 0x54000 <= x.
Proof. pose proof DEPS as DEPS'; clear DEPS'. intros Hx. ctx_tac_all. clear - Hx C17 C18 C24. lia. Qed.
Lemma newbits_val : bv_unsigned (sv_denot Et NEWBITS) = 4064 + NEEDED.
Proof.
pose proof DEPS as DEPS'; clear DEPS'.
vals_tac. pose proof ctx_lin as CL. destruct CL as (_ & _ & _ & _ & _ & N6 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & O22 & _).
pose proof (needed_rangeG L A regs mem md g am fr n a ka rg HC) as (_ & _ & N3). change (needed fr n) with NEEDED in N3.
pose proof (shape ubs2_msyms L A mem md g am fr MX (rc_used _ _ _ _ _ _ _ _ _ _ _ _ HC) (rc_fr _ _ _ _ _ _ _ _ _ _ _ _ HC) (rc_63 _ _ _ _ _ _ _ _ _ _ _ _ HC)) as (Hl & Hml & _).
pose proof (fp_vals _ _ _ _ FP) as V. cbn in V. destruct V as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Vml & _).
change (fv_ml VV) with (am_maplen am) in Vml.
unfold NEWBITS. cbn [sv_denot]. rewrite alu64_or, alu64_and, !ewT, !Z.add_0_r, VBITS, VNEED.
assert (EB : meta_bits am = 4064 + 4096 * am_maplen am) by (unfold meta_bits; rewrite Hl, (rc_63 _ _ _ _ _ _ _ _ _ _ _ _ HC); lia).
rewrite EB. rewrite !lit64_small by lia.
assert (A1 : Z.land (4064 + 4096 * am_maplen am) 4095 = 4064).
{ change 4095 with (Z.ones 12). rewrite Z.land_ones by lia. change (2 ^ 12) with 4096.
replace (4064 + 4096 * am_maplen am) with (4064 + am_maplen am * 4096) by lia. rewrite Z_mod_plus_full. reflexivity. }
rewrite A1. pose proof (Z_div_mod_eq_full NEEDED 4096) as DM. rewrite N6, Z.add_0_r in DM.
assert (L0 : Z.land 4064 NEEDED = 0).
{ rewrite DM. apply Z.bits_inj'. intros k Hk. rewrite Z.land_spec, Z.bits_0.
destruct (Z_lt_le_dec k 12) as [Hk'|Hk'].
- replace (4096 * (NEEDED / 4096)) with ((NEEDED / 4096) * 2 ^ 12) by (change (2 ^ 12) with 4096; lia).
rewrite Z.mul_pow2_bits by lia. rewrite (Z.testbit_neg_r _ (k - 12)) by lia. apply Bool.andb_false_r.
- replace 4064 with (254 * 2 ^ 4) by reflexivity. rewrite Z.mul_pow2_bits by lia.
rewrite (Z.bits_above_log2 254 (k - 4)); [reflexivity | lia |]. cbn. lia. }
rewrite <- Z.lxor_lor by exact L0. rewrite <- Z.add_nocarry_lxor by exact L0. reflexivity.
Qed.
Lemma newh3_val : bv_unsigned (sv_denot Et (match t with R14 => NEWH3_14 | _ => NEWH3 t end)) = 32 * RC'.
Proof.
pose proof DEPS as DEPS'; clear DEPS'.
vals_tac. ctx_tac. pose proof WRSV_val as W.
destruct t_cases as [[R ->]|[[R ->]|[[R ->]|[R ->]]]]; unfold RC'.
- cbn [sv_denot NEWH3]. rewrite alu64_or, ewT, Z.add_0_r, VIDX, !lit64_small by lia. rewrite Z.lor_0_r. destruct (Z.leb_spec 5 RSV'); lia.
- unfold NEWH3_14. cbn [sv_denot]. fold (sv_denot Et WRSV).
change (sext 64 (alu32 ALU_SUB (low32 (sv_denot Et (SOff aNEND 0))) (low32 (sv_denot Et (SOff aNPN 0))))) with (sv_denot Et WRSV).
rewrite alu64_or, alu64_sll, alu64_add, W, ewT, Z.add_0_r, VIDX, !lit64_small by lia. rewrite Z.lor_0_r.
unfold add64, sll64. rewrite Z.add_0_r, (Z.mod_small RSV') by lia. change (5 mod 64) with 5. rewrite Z.shiftl_mul_pow2 by lia. change (2 ^ 5) with 32.
rewrite Z.mod_small by lia. destruct (Z.leb_spec 5 RSV'); lia.
- cbn [sv_denot NEWH3]. rewrite alu64_or, ewT, Z.add_0_r, VIDX, !lit64_small by lia. rewrite Z.lor_0_r. destruct (Z.leb_spec 5 RSV'); lia.
- cbn [sv_denot NEWH3]. rewrite alu64_or, ewT, Z.add_0_r, VIDX, !lit64_small by lia. rewrite Z.lor_0_r. destruct (Z.leb_spec 5 RSV'); lia.
Qed.
Lemma final_read (base : nat) (stk : YQ0b.region) (ss : sstate) (msF : machine_state) (RETimg : RET_img) :
st_ok ubs2segs Et ss msF -> ss_mem ss = tail_mem_final base stk t -> xvt base = RET ->
callee_view ss = callee_view0 -> sr_get (ss_regs ss) 10 = SOff aNP 0 ->
r_base stk = Some aSP -> r_wlo stk = -8256 -> r_whi stk = 0 ->
let mF := ms_mem msF in
bytes_at ubs2_msyms mF (NP - 4) 1 0 /\ bytes_at ubs2_msyms mF (NP - 3) 1 (32 * RC') /\ bytes_at ubs2_msyms mF (NP - 2) 2 OFF /\
bytes_at ubs2_msyms mF (G + 16) 8 RET /\ bytes_at ubs2_msyms mF (G + 24) 4 0 /\ bytes_at ubs2_msyms mF (G + 28) 4 0 /\
bytes_at ubs2_msyms mF (G + 32) 8 (4064 + NEEDED) /\ bytes_at ubs2_msyms mF NEND 1 0 /\
(0 < RSV' -> bytes_at ubs2_msyms mF NPN 1 0) /\
(5 <= RSV' -> bytes_at ubs2_msyms mF (NEND - 4) 4 RSV' /\ bytes_at ubs2_msyms mF (NEND - 5) 1 0) /\
(forall x, STK x \/ ERRN x -> writable_at ubs2segs mF x) /\
(forall x, (NP - 4 <= x < NP) \/ (G + 16 <= x < G + 40) \/ (0 < RSV' /\ x = NPN) \/ (5 <= RSV' /\ NEND - 5 <= x <= NEND) \/ x = NEND -> present mF x) /\
regs_preserved regs (ms_regs msF) /\ getr (ms_regs msF) 10 = Z_to_bv 64 NP /\ ew Et 1 = getr regs 1.
Proof.
pose proof DEPS as DEPS'; clear DEPS'.
intros HS Hsm Hb Hcv Ha0 B1 B2 B3. cbv zeta. vals_tac. ctx_tac. pose proof newbits_val as NB. pose proof newh3_val as NH.
pose proof (shape ubs2_msyms L A mem md g am fr MX (rc_used _ _ _ _ _ _ _ _ _ _ _ _ HC) (rc_fr _ _ _ _ _ _ _ _ _ _ _ _ HC) (rc_63 _ _ _ _ _ _ _ _ _ _ _ _ HC)) as (_ & _ & Hav & Hfd & _).
pose proof (st_ok_mem_ok ubs2segs Et _ _ HS) as (_ & ROK & _). rewrite Hsm in ROK. unfold tail_mem_final in ROK.
apply Forall_app in ROK as [R9 RT].
apply Forall_cons_iff in R9 as [Rarea R9]. apply Forall_cons_iff in R9 as [Rctx R9]. apply Forall_cons_iff in R9 as [Rnl R9].
apply Forall_cons_iff in R9 as [Rstk R9]. apply Forall_cons_iff in R9 as [Rgot R9]. apply Forall_cons_iff in R9 as [Rguard R9].
apply Forall_cons_iff in R9 as [Rerr R9]. apply Forall_cons_iff in R9 as [Rmeta R9]. apply Forall_cons_iff in R9 as [Rhdr _].
destruct Rstk as (_ & _ & Wstk & _). rewrite B1, B2, B3, baseT, VSP in Wstk.
destruct Rerr as (_ & _ & Werr & _). cbn [r_base r_wlo r_whi reg_errnoR] in Werr. rewrite baseT, VTP in Werr.
destruct Rmeta as (_ & _ & Wmeta & Kmeta). cbn [r_base r_wlo r_whi r_chunks] in Wmeta, Kmeta. rewrite baseT, VG in Wmeta, Kmeta.
destruct Rhdr as (_ & _ & Whdr & Khdr). cbn [r_base r_wlo r_whi r_chunks] in Whdr, Khdr. rewrite baseT, VNP in Whdr, Khdr.
apply Forall_cons_iff in Kmeta as [K32 Kmeta]. apply Forall_cons_iff in Kmeta as [K16 Kmeta]. apply Forall_cons_iff in Kmeta as [K24 Kmeta]. apply Forall_cons_iff in Kmeta as [K28 _].
apply Forall_cons_iff in Khdr as [Kh3 Khdr]. apply Forall_cons_iff in Khdr as [Kh4 Khdr]. apply Forall_cons_iff in Khdr as [Kh2 _].
assert (TT : (forall x, (0 < RSV' /\ x = NPN) \/ (5 <= RSV' /\ NEND - 5 <= x <= NEND) \/ x = NEND -> writable_at ubs2segs (ms_mem msF) x) /\
bytes_at ubs2_msyms (ms_mem msF) NEND 1 0 /\ (0 < RSV' -> bytes_at ubs2_msyms (ms_mem msF) NPN 1 0) /\
(5 <= RSV' -> bytes_at ubs2_msyms (ms_mem msF) (NEND - 4) 4 RSV' /\ bytes_at ubs2_msyms (ms_mem msF) (NEND - 5) 1 0)).
{ pose proof WRSV_val as W.
assert (E1 : NEND = RET + NEEDED - 4) by reflexivity. assert (E2 : NPN = NP + n) by reflexivity.
assert (E3 : NP = RET + 16 + 16 * OFF) by reflexivity. assert (E4 : RSV' = NEEDED - 20 - 16 * OFF - n) by reflexivity.
destruct t_cases as [[R X]|[[R X]|[[R X]|[R X]]]]; rewrite X in RT; cbn in RT.
- apply Forall_cons_iff in RT as [(_ & _ & W1 & KC1) _]. cbn [r_base r_wlo r_whi r_chunks] in W1, KC1. rewrite baseT, VNEND in W1, KC1.
apply Forall_cons_iff in KC1 as [KC1 _].
split; [intros x Hx; replace x with (NEND + 0) by lia; apply W1; lia|].
split; [replace NEND with (NEND + 0) by lia; eapply (chunk_bytes _ _ _ _ _ _ _ KC1); [reflexivity | cbn; lia]|]. split; intros; lia.
- apply Forall_cons_iff in RT as [(_ & _ & W1 & KC1) RT]. apply Forall_cons_iff in RT as [(_ & _ & W2 & KC2) _].
cbn [r_base r_wlo r_whi r_chunks] in W1, KC1, W2, KC2. rewrite baseT, VNEND in W1, KC1. rewrite baseT, VNPN in W2, KC2.
apply Forall_cons_iff in KC1 as [KC1 _]. apply Forall_cons_iff in KC2 as [KC2 _].
split; [intros x Hx; destruct (Z.eq_dec x NPN); [subst x; replace NPN with (NPN + 0) by lia; apply W2; lia | replace x with (NEND + 0) by lia; apply W1; lia]|].
split; [replace NEND with (NEND + 0) by lia; eapply (chunk_bytes _ _ _ _ _ _ _ KC1); [reflexivity | cbn; lia]|].
split; [intros _; replace NPN with (NPN + 0) by lia; eapply (chunk_bytes _ _ _ _ _ _ _ KC2); [reflexivity | cbn; lia] | intros; lia].
- apply Forall_cons_iff in RT as [(_ & _ & W1 & KC1) _]. cbn [r_base r_wlo r_whi r_chunks] in W1, KC1. rewrite baseT, VNEND in W1, KC1.
apply Forall_cons_iff in KC1 as [K14 KC1]. apply Forall_cons_iff in KC1 as [K15 KC1]. apply Forall_cons_iff in KC1 as [K10 _].
split; [intros x Hx; replace x with (NEND + (x - NEND)) by lia; apply W1; lia|].
split; [replace NEND with (NEND + 0) by lia; eapply (chunk_bytes _ _ _ _ _ _ _ K10); [reflexivity | cbn; lia]|].
split; [intros _; replace NPN with (NEND + -5) by lia; eapply (chunk_bytes _ _ _ _ _ _ _ K15); [reflexivity | cbn; lia]|].
intros _. split; [replace (NEND - 4) with (NEND + -4) by lia; eapply (chunk_bytes _ _ _ _ _ _ _ K14); [cbn [sv_denot]; rewrite lit64_small by lia; lia | cbn; lia]|].
replace (NEND - 5) with (NEND + -5) by lia. eapply (chunk_bytes _ _ _ _ _ _ _ K15); [reflexivity | cbn; lia].
- apply Forall_cons_iff in RT as [(_ & _ & W1 & KC1) RT]. apply Forall_cons_iff in RT as [(_ & _ & W2 & KC2) _].
cbn [r_base r_wlo r_whi r_chunks] in W1, KC1, W2, KC2. rewrite baseT, VNEND in W1, KC1. rewrite baseT, VNPN in W2, KC2.
apply Forall_cons_iff in KC1 as [K14 KC1]. apply Forall_cons_iff in KC1 as [K15 KC1]. apply Forall_cons_iff in KC1 as [K10 _]. apply Forall_cons_iff in KC2 as [KC2 _].
split; [intros x Hx; destruct (Z.eq_dec x NPN); [subst x; replace NPN with (NPN + 0) by lia; apply W2; lia | replace x with (NEND + (x - NEND)) by lia; apply W1; lia]|].
split; [replace NEND with (NEND + 0) by lia; eapply (chunk_bytes _ _ _ _ _ _ _ K10); [reflexivity | cbn; lia]|].
split; [intros _; replace NPN with (NPN + 0) by lia; eapply (chunk_bytes _ _ _ _ _ _ _ KC2); [reflexivity | cbn; lia]|].
intros _. split; [replace (NEND - 4) with (NEND + -4) by lia; eapply (chunk_bytes _ _ _ _ _ _ _ K14); [exact W | cbn; lia]|].
replace (NEND - 5) with (NEND + -5) by lia. eapply (chunk_bytes _ _ _ _ _ _ _ K15); [reflexivity | cbn; lia]. }
destruct TT as (TW1 & TB1 & TB2 & TB3).
repeat match goal with |- _ /\ _ => split end.
- replace (NP - 4) with (NP + -4) by lia. eapply (chunk_bytes _ _ _ _ _ _ _ Kh4); [reflexivity | cbn; lia].
- replace (NP - 3) with (NP + -3) by lia. eapply (chunk_bytes _ _ _ _ _ _ _ Kh3); [exact NH | cbn; lia].
- replace (NP - 2) with (NP + -2) by lia. eapply (chunk_bytes _ _ _ _ _ _ _ Kh2); [rewrite (U_off0 _ XRt), VOFF; reflexivity | cbn; lia].
- eapply (chunk_bytes _ _ _ _ _ _ _ K16); [rewrite (U_off0 _ XRt); exact Hb | cbn; lia].
- eapply (chunk_bytes _ _ _ _ _ _ _ K24); [rewrite (U_off0 _ XRt), VAV, Hav; reflexivity | cbn; lia].
- eapply (chunk_bytes _ _ _ _ _ _ _ K28); [rewrite (U_off0 _ XRt), VFR, Hfd; reflexivity | cbn; lia].
- eapply (chunk_bytes _ _ _ _ _ _ _ K32); [exact NB | cbn; lia].
- exact TB1.
- exact TB2.
- exact TB3.
- intros x [Hx|Hx].
+ unfold STK in Hx. replace x with (SP + (x - SP)) by lia. apply Wstk. lia.
+ unfold ERRN in Hx. rewrite ERRNO2_val in Hx. replace x with (ubs2_tp + (x - ubs2_tp)) by lia. apply Werr. lia.
- intros x Hx. unfold NPN in *. unfold NP, NEND in *.
destruct Hx as [Hx|[Hx|Hx]].
+ apply off_img_writable_present; [lia | apply (new_off_img _ RETimg); lia |].
specialize (Whdr (x - (RET + 16 + 16 * OFF)) ltac:(lia)). replace (RET + 16 + 16 * OFF + (x - (RET + 16 + 16 * OFF))) with x in Whdr by lia. exact Whdr.
+ apply off_img_writable_present; [lia | apply meta_off_img; lia |].
specialize (Wmeta (x - G) ltac:(lia)). replace (G + (x - G)) with x in Wmeta by lia. exact Wmeta.
+ apply off_img_writable_present; [lia | apply (new_off_img _ RETimg); lia | apply TW1; exact Hx].
-
intros r0 Hr0. destruct (callee_saved_cases r0 Hr0) as [Rr RI]. rewrite (Z_to_bv5_nat_to_reg r0 Rr).
pose proof (st_ok_regs_ok ubs2segs Et _ _ HS) as RG.
unfold callee_view, callee_view0, view in Hcv.
assert (GR : forall i, In i [2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%nat -> sr_get (ss_regs ss) (nat_to_reg i) = SOff i 0).
{ intros i Hi. cbn [map] in Hcv.
repeat (destruct Hi as [<-|Hi]; [
match goal with |- sr_get _ (nat_to_reg ?k) = _ =>
exact (f_equal (fun l => List.nth (match k with 2 => 1 | 3 => 2 | 4 => 3 | 8 => 4 | 9 => 5 | 18 => 6 | 19 => 7 | 20 => 8 | 21 => 9 | 22 => 10 | 23 => 11 | 24 => 12 | 25 => 13 | 26 => 14 | _ => 15 end)%nat l (SLit 0)) Hcv) end |]).
destruct Hi. }
rewrite (RG (nat_to_reg (Z.to_nat r0))), (GR _ RI), denT, xvt_lo by (cbn in RI; unfold Nat.lt; repeat (destruct RI as [<-|RI]; [cbv; lia|]); destruct RI).
unfold xvr. replace (Z.to_nat r0 <? 96)%nat with true by (symmetry; apply Nat.ltb_lt; cbn in RI; repeat (destruct RI as [<-|RI]; [cbv; lia|]); destruct RI).
rewrite xvf_reg by (cbn in RI; repeat (destruct RI as [<-|RI]; [cbv; lia|]); destruct RI). change (fv_regs VV) with regs. apply Z_to_bv_bv_unsigned.
- rewrite (st_ok_regs_ok ubs2segs Et _ _ HS 10%bv), Ha0, denT, VNP. reflexivity.
- unfold Et, EV. cbn [ew]. rewrite V1. apply Z_to_bv_bv_unsigned.
Qed.
End h.
End f.
