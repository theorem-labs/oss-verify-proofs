(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require BvWfKernel.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.jsoncons.fuzz_ubjson_parser_max.images Require Import Ubsan.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import
PropExec CatExec CatSim SeqExec StoreOk ShapeAlg DivergeSim SpinAlg SpinAlgX Nodes AgentLib SpecConsts
SymExec SymExec2 SymExec2Sound SymRun SymDrive SymDriveX LibKnowFrame
Hoare Ju0ExitBase Ju0StdioDefs Ju0StdioWrite.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import SecKit.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import SX2. Import SX2S.
Open Scope Z_scope.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require TCodec.
Ltac2 tcn__Ju0LibStdioCall () := ([""; "Corelib.Init.Datatypes."; "Corelib.Init.Logic."; "Corelib.Init.Nat."; "Corelib.Init.Peano."; "Corelib.Lists.ListDef."; "Corelib.Numbers.BinNums."; "LinuxProcessSemantics.LinuxProcessSem.Run."; "LinuxProcessSemantics.LinuxProcessSem.State."; "LinuxProcessSemantics.Riscv.Prelude."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.Ju0LibStdioCall.FPX_1."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.Ju0StdioDefs."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.LibKnowFrame."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PropExec."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.ShapeAlg."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.SpinAlg."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.StoreOk."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.SymDrive."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.SymDriveX."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.SymExec2.SX2."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.SymExec2Sound.SX2S."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.SymRun."; "OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.Ubsan.M."; "Stdlib.Lists.List."; "Stdlib.ZArith.BinInt.Z."; "stdpp.bitvector.definitions."], [["1None"; "1O"; "1Some"; "1app"; "1bool"; "1false"; "1length"; "1list"; "1nat"; "1nil"; "1option"; "1pair"; "1prod"; "1true"; "2and"; "2eq"]; ["2ex"; "2iff"; "2not"; "2or"; "3sub"; "4le"; "4lt"; "5map"; "5nth"; "6Z"; "0E"; "0K"; "7mkCfg"; "8FdChannel"; "8FdEntry"; "8Model"]; ["8WriteEv"; "8event"; "8fd_lookup"; "8m_fds"; "8m_halted"; "8m_vm_lazy"; "9bvmap"; "0M"; "0M'"; "0R"; "0R'"; ":hi_ok"; ":inr"; ":kimg_cut"; ":sc_bufp"; ":sc_bufsz"]; [":sc_f"; ":sc_fd"; ":sc_kn"; ":sc_l"; ":sc_ret"; ":sc_s"; ":sc_sp"; ":sc_sr"; ":sc_wb"; ":sc_wp"; ":stdio_call"; ":stdio_res"; ";sw_post"; "<kn_frame"; "=mkst"; "=rdn"]; ["=seg_rom"; ">TSet"; ">t_emit"; "?srealizes"; "@mem_grows"; "Ajunk_vals"; "Asr_after_call_j"; "Bkindex"; "CELit"; "CEnv"; "CSA"; "Cedenot"; "Cenv"; "Cexpr"; "Ckentry"; "Cridx"]; ["Csplit_lit"; "Csr_get"; "Csr_upd"; "Destart"; "Dflat"; "Dknow_ok"; "Dregs_ok"; "Eexpr_vars_lt"; "Evals_ev"; "Floaded_segments"; "Gnth_error"; "Hadd"; "Hle"; "Hlt"; "Hof_nat"; "Hpow"]; ["Hsub"; "0a"; "0b"; "0b1"; "0b2"; "0b3"; "0e"; "0ebs"; "0extra"; "0fx"; "0i"; "0j"; "0k"; "0kept"; "0kn"; "0l"]; ["0lo"; "0m"; "0model"; "0n"; "0n1"; "0n2"; "0n3"; "0nv"; "0o1"; "0o2"; "0o3"; "0off"; "0p"; "0pending"; "0res"; "0s"]; ["0scfg"; "0sr"; "IZ_to_bv"; "Ibv"; "Ibv_unsigned"; "0su"; "0vals"; "0wb"; "0wp"; "0x"]]).
#[local] Abbreviation RSEGS := Ubsan.M.loaded_segments.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Section FPX_1. Context {fx : PropExec.FPState}.
Variable scfg : SpuriousCfg.
Definition SC_KEPT : list nat := [1; 2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%nat.
Record stdio_res : Type := SCR_ {
sc_f : Z;
sc_fd : Z;
sc_ret : Z;
sc_wb : expr;
sc_wp : expr;
sc_bufp : expr;
sc_bufsz : expr;
sc_s : expr;
sc_l : expr;
sc_sp : expr;
sc_sr : list expr;
sc_kn : list kentry
}.
Definition hi_ok (kn : list kentry) (e : expr) : bool :=
match erange kn e with Some (_, hi) => Z.leb hi 0x800000000000 | None => false end.
Lemma hi_ok_sound : ltac2:(TCodec.tc2 tcn__Ju0LibStdioCall "Q7'R<'T3yR0%211':y8%511%311p051'7'R>%211'R=&RE&RIr4r3r2%544321'?'4&Q;%1265(=%53421&RL&T4&R;r6%221=%42L1+TPPPPPPPP0%7221p091p0@1pV>G1pVNI1pR@M1pQFQ61").
Proof.
intros E M kn e HK H. unfold hi_ok in H.
destruct (erange kn e) as [[lo hi]|] eqn:He; [|discriminate].
pose proof (erange_sound RSEGS E M kn e lo hi HK He). apply Z.leb_le in H. lia.
Qed.
Definition lit_even_ret (e : expr) : option Z :=
match e with
| ELit r => if ((r mod 2 =? 0) && (0 <=? r) && (r <? two64))%bool then Some r else None
| _ => None
end.
Definition kimg_cut1 (a n : Z) (K : kentry) : list kentry :=
match K with
| KImg lo hi =>
if (Z.leb hi a || Z.leb (a + n) lo)%bool then [K]
else (if Z.ltb lo a then [KImg lo a] else []) ++ (if Z.ltb (a + n) hi then [KImg (a + n) hi] else [])
| _ => [K]
end.
Definition kimg_cut (k : list kentry) (a n : Z) : list kentry := List.flat_map (kimg_cut1 a n) k.
Definition stdio_call (nv : nat) (sr : list expr) (kn : list kentry) : option stdio_res :=
match nth 10 sr (ELit 0), lit_even_ret (nth 1 sr (ELit 0)) with
| ELit f, Some ret =>
match kread RSEGS kn (ELit 0) (f + 120) 4, kread RSEGS kn (ELit 0) (f + 40) 8, kread RSEGS kn (ELit 0) (f + 56) 8,
kread RSEGS kn (ELit 0) (f + 88) 8, kread RSEGS kn (ELit 0) (f + 96) 8,
kread RSEGS kn (ELit 0) 0xb5f18 8, kblob_find kn (ELit 0) 0xe8f20 with
| Some (ELit fd), Some wp, Some wb, Some bufp, Some bufsz, Some (ELit cg), Some (clen, _) =>
let sp := nth 2 sr (ELit 0) in
let '(qb, k0) := split_lit sp in
let qk := (k0 - 112)%Z in
match kindex (is_kwr_cov qb qk 112) kn 0, base_range kn qb with
| Some _, Some (blo, bhi) =>
if ((0xb6000 <=? f) && (f + 232 <=? 0xe8f20)
&& ((fd =? 1) || (fd =? 2)) && (cg mod two64 =? 0xe8f20)
&& (4294967296 + 112 <=? blo + k0) && (bhi + k0 <=? 0x800000000000)
&& expr_eqb clen (ELit 8)
&& expr_vars_lt nv bufp && expr_vars_lt nv bufsz
&& sr_vars_lt nv sr && kn_vars_lt nv kn && Nat.eqb (length sr) 32)%bool
then
let k0 := kimg_cut (kimg_cut kn (f + 32) 16) (f + 56) 8 in
let k1 := kn_frame k0 qb qk 112 in
let k2 := kn_frame k1 (ELit 0) (f + 32) 16 in
let k3 := kn_frame k2 (ELit 0) (f + 56) 8 in
Some (SCR_ f fd ret wb wp bufp bufsz (nth 11 sr (ELit 0)) (nth 12 sr (ELit 0)) sp
(sr_upd (sr_after_call_j sr SC_KEPT nv) 10 (nth 12 sr (ELit 0)))
(KWord (SA (ELit 0) (f + 32)) 8 (mkAlu ALU_ADD bufp bufsz)
:: KWord (SA (ELit 0) (f + 40)) 8 bufp
:: KWord (SA (ELit 0) (f + 56)) 8 bufp :: k3))
else None
| _, _ => None
end
| _, _, _, _, _, _, _ => None
end
| _, _ => None
end.
Definition inr (lo n : Z) (x : word) : bool := (Z.leb lo (bv_unsigned x) && Z.ltb (bv_unsigned x) (lo + n))%bool.
Lemma inr_spec : ltac2:(TCodec.tc2 tcn__Ju0LibStdioCall "L'I'T3yR0%211&A'?'4&Q<r3r2r1%43321(=%83721'>&RL&T4%12?7%32:1&RM&RK%12=<%3251%9251%D2;1pXDF1pW8J1pW2K1").
Proof. intros lo n x. unfold inr. rewrite andb_true_iff, Z.leb_le, Z.ltb_lt. tauto. Qed.
Lemma inr_false : ltac2:(TCodec.tc2 tcn__Ju0LibStdioCall "N'I'T3yR0%211&A'?'4&Q<r3r2r1%43321(5%83721&B'>&RL&T4%12@8%32;1&RM&RK%12>=%3251%9251%;11%F2=1pXDH1pW8L1pW2M1").
Proof. intros lo n x. rewrite <- inr_spec. destruct (inr lo n x); split; congruence. Qed.
Lemma know_ok_frame3 : ltac2:(TCodec.tc2 tcn__Ju0LibStdioCall "S>'R<'T3yR0%211':y8%511%311p051pXD62'7'R>%211'R='I&RE&RIr=r<r:%544321&RDr>(R:r9%2261r8%63521r?r7%7241r6%;3421r@r5%<241r4%@3421&B'>&RL&RCrB%D2EJ%3221&T4r1%22Q=1%8241&RM&RK%127Q1%3251%>251%@11rCr;%Q22Q71%A231r2%?2QJ1%E231%<24Q;%>231%I231%K11rD%J21Q:r3%H2R31%N231%E24Q=%G231%Q2231%Q411'?%E1Q8%;1Q9%33R721p051p0?1p0K1pXDR?1&R4rA%221QD&QM%14QFQKR1R6%241R6Q0R5%341R1QOQL%R;4R:Q361p061p0:1p0QH1p0QN1p0R41p0R<1pW>RC1pWFRD1pV<RF1pW<RF1pWDRG1pV:RI1pW:RI1pWBRJ1pV8RL1pVNRN1pRBS21pR@S41pQFS=1").
Proof.
intros E M M' kn b1 o1 n1 b2 o2 n2 b3 o3 n3 HK F1 F2 F3 Hout Hg.
set (a1 := estart E (SA b1 o1)) in *. set (a2 := estart E (SA b2 o2)) in *. set (a3 := estart E (SA b3 o3)) in *.
set (M1 := fun x : word => if (inr a2 n2 x || inr a3 n3 x)%bool then M x else M' x).
set (M2 := fun x : word => if inr a3 n3 x then M x else M' x).
assert (O1 : forall x : word, (bv_unsigned x < a1 \/ a1 + n1 <= bv_unsigned x)%Z -> M1 x = M x).
{ intros x Hx. unfold M1. destruct (inr a2 n2 x) eqn:E2; [reflexivity|]. destruct (inr a3 n3 x) eqn:E3; [reflexivity|].
cbn [orb]. apply inr_false in E2. apply inr_false in E3. apply Hout; [lia | exact E2 | exact E3]. }
assert (G1 : mem_grows M M1).
{ intros x Hx. unfold M1. destruct (inr a2 n2 x || inr a3 n3 x)%bool; [exact Hx | exact (Hg x Hx)]. }
assert (O2 : forall x : word, (bv_unsigned x < a2 \/ a2 + n2 <= bv_unsigned x)%Z -> M2 x = M1 x).
{ intros x Hx. unfold M1, M2. destruct (inr a3 n3 x) eqn:E3; [rewrite orb_true_r; reflexivity|].
destruct (inr a2 n2 x) eqn:E2; [|reflexivity]. apply inr_spec in E2. lia. }
assert (G2 : mem_grows M1 M2).
{ intros x Hx. unfold M1, M2 in *. destruct (inr a3 n3 x); [rewrite orb_true_r in Hx; exact Hx|].
destruct (inr a2 n2 x); cbn [orb] in Hx; [exact (Hg x Hx) | exact Hx]. }
assert (O3 : forall x : word, (bv_unsigned x < a3 \/ a3 + n3 <= bv_unsigned x)%Z -> M' x = M2 x).
{ intros x Hx. unfold M2. destruct (inr a3 n3 x) eqn:E3; [|reflexivity]. apply inr_spec in E3. lia. }
assert (G3 : mem_grows M2 M').
{ intros x Hx. unfold M2 in Hx. destruct (inr a3 n3 x); [exact (Hg x Hx) | exact Hx]. }
eapply know_ok_frame; [| exact F3 | exact O3 | exact G3].
eapply know_ok_frame; [| exact F2 | exact O2 | exact G2].
eapply know_ok_frame; [exact HK | exact F1 | exact O1 | exact G1].
Qed.
Lemma Forall_one' : forall {A} (P : A -> Prop) x, P x -> Forall P [x].
Proof. intros A P x H. constructor; [exact H | constructor]. Qed.
Lemma kimg_cut_sound : ltac2:(TCodec.tc2 tcn__Ju0LibStdioCall "N'R<'T3yR0%211':y8%511%311p051'7'R>%211'I&RE&RIr5r4r3%544321r6&Q=r2%23651%:49481p061pW8=1pV4>1pVJ@1pR@D1pQFM1").
Proof.
intros E M k a n HK. unfold kimg_cut, know_ok. apply Forall_flat_map. apply Forall_forall. intros K Hin.
pose proof (proj1 (Forall_forall _ _) HK K Hin) as HKK.
destruct K as [| | |lo hi| | | |]; cbn [kimg_cut1]; try (apply Forall_one'; exact HKK).
destruct (Z.leb hi a || Z.leb (a + n) lo)%bool eqn:Hap; [apply Forall_one'; exact HKK|].
apply Bool.orb_false_iff in Hap as [Hap1 Hap2]. apply Z.leb_gt in Hap1. apply Z.leb_gt in Hap2.
cbn [kentry_ok] in HKK. destruct HKK as (H0 & Hhi & Himg).
apply Forall_app. split.
- destruct (Z.ltb lo a) eqn:E1; [|constructor]. apply Z.ltb_lt in E1. apply Forall_one'. cbn [kentry_ok].
split; [lia|]. split; [lia|]. intros i Hi. apply Himg. lia.
- destruct (Z.ltb (a + n) hi) eqn:E2; [|constructor]. apply Z.ltb_lt in E2. apply Forall_one'. cbn [kentry_ok].
split; [lia|]. split; [lia|]. intros i Hi. apply Himg. lia.
Qed.
Lemma u_lit0 : ltac2:(TCodec.tc2 tcn__Ju0LibStdioCall ">'R<'?'I&T4yR0&R;r1(R8z%211%5241%8271%;3:14pQF=1").
Proof. intros E. cbn [edenot]. apply u64_lit. lia. Qed.
Lemma flat_abs0 : ltac2:(TCodec.tc2 tcn__Ju0LibStdioCall "Q1'R<'I&RLzr2%3221&RKr4r3%3221&RO+2+R0%3221%<251&RMr5%2214&RDr7(R:(R8%11Cr6%4221%73619p091p0=1p0G1p0H1pW8M1pWHN1pQFQ01").
Proof. intros E off n H0 Hn Hnw Hlt. unfold flat, estart. cbn [a_base a_off]. rewrite u_lit0. lia. Qed.
Section SE.
Local Abbreviation SEC_T_split_lit_denot := (ltac2:(TCodec.tc2 tcn__Ju0LibStdioCall "Q2'R<'R='I'?'<%1243&R@r3%211(;r2r1%34;:21%:3851'T3yR0%211&R;r5r4%3221&T2&RK&T4%726A%22:1%421@%62<1%I3<81p0@1pVJL1pV6N1pV>O1pQFQ11")) (only parsing).
Variable E : ltac:(sec_ty2 constr:(SEC_T_split_lit_denot) 0%nat 0%nat).
Lemma split_lit_denot : ltac:(sec_stmt2 constr:(SEC_T_split_lit_denot) 1%nat 0%nat).
Proof.
intros e b k H.
assert (G : forall e' : expr, edenot E e' = Z_to_bv 64 (bv_unsigned (edenot E e') + 0)).
{ intros e'. rewrite Z.add_0_r. symmetry. apply Z_to_bv_bv_unsigned. }
unfold split_lit in H.
destruct e; try (injection H as <- <-; apply G).
- injection H as <- <-. cbn [edenot]. rewrite u64_lit by lia. rewrite Z.add_0_l. reflexivity.
- lazymatch type of H with (match ?o with _ => _ end = _) => destruct o end; try (injection H as <- <-; apply G).
lazymatch type of H with (match ?y with _ => _ end = _) => destruct y end; try (injection H as <- <-; apply G).
injection H as <- <-. cbn [edenot]. rewrite alu_add. unfold v_add. apply bv_eq.
rewrite !Z_to_bv_unsigned, !bv_wrap64_mod. rewrite Z.add_mod_idemp_r by lia. reflexivity.
Qed.
End SE.
Lemma split_lit_vars : ltac2:(TCodec.tc2 tcn__Ju0LibStdioCall "N'8'R='I'?'<%1243&R@r3%211(;r2r1%34;:21%:3851'4&RGr5r4%3221(=%A3621r6%7215%D3914p041p0<1pVJH1pV6J1pV>K1pW8M1").
Proof.
intros n e b k H Hv. unfold split_lit in H.
destruct e; try (injection H as <- <-; first [reflexivity | exact Hv]).
lazymatch type of H with (match ?o with _ => _ end = _) => destruct o end; try (injection H as <- <-; exact Hv).
lazymatch type of H with (match ?y with _ => _ end = _) => destruct y end; try (injection H as <- <-; exact Hv).
injection H as <- <-. cbn [expr_vars_lt] in Hv. apply andb_prop in Hv as [Hv _]. exact Hv.
Qed.
Lemma kindex_some : ltac2:(TCodec.tc2 tcn__Ju0LibStdioCall "Q;'R>'4p021'7%114'8'?':%113&R7r4r3r2%43321(2r1%22;1%;3941'@'>%=1D&RJr5&D%12=>%43I31%<2J;%E3721r6%11>(=%I3N21'E%12GF%?231%@281qQHQ41%C2Q51p0E1pVHQ21pVFQ31pVNQ51pWJQ81").
Proof.
intros p kn. induction kn as [|K rest IH]; intros i j H; cbn [kindex] in H; [discriminate|].
destruct (p K) eqn:HP.
- injection H as <-. exists K. rewrite Nat.sub_diag. cbn. auto.
- destruct (IH (S i) j H) as (K' & Hn & HP' & Hle). exists K'.
replace (j - i)%nat with (S (j - S i))%nat by lia. cbn [nth_error]. repeat split; try assumption. lia.
Qed.
Lemma ridx_lit : ltac2:(TCodec.tc2 tcn__Ju0LibStdioCall "A'8&Fr1uQ0%3221'?&R?&T2y5&RNr2%211%5241%711%93>14p0;1pW8@1").
Proof.
intros n Hn. unfold ridx. rewrite Z_to_bv_unsigned. unfold bv_wrap.
change (bv_modulus 5) with 32%Z. rewrite Z.mod_small by lia. lia.
Qed.
Lemma sr_get_nat : ltac2:(TCodec.tc2 tcn__Ju0LibStdioCall "O'7'R=%211'8'>&F(1r1%3221uQ0%5231%7231'?&RAr3&T2y5&RNr2%211%5241%8271&H(R8z%211%44I8<1%?3J61p0A1pW8J1pX4L1").
Proof.
intros sr n Hn. unfold sr_get.
assert (Hnz : bv_eqb (Z_to_bv 5 (Z.of_nat n)) 0%bv = false).
{ unfold bv_eqb. apply Z.eqb_neq. rewrite Z_to_bv_unsigned. unfold bv_wrap.
change (bv_modulus 5) with 32%Z. rewrite Z.mod_small by lia.
replace (bv_unsigned (0%bv : bv 5)) with 0%Z by reflexivity. lia. }
rewrite Hnz, ridx_lit by lia. reflexivity.
Qed.
Lemma length_sr_upd : ltac2:(TCodec.tc2 tcn__Ju0LibStdioCall "E'7'R=%211'8&Fr2&6r3%2271%5241'?&RBr4%23168%82=1%92>3%63=21p081pV>A1pW8@1pX4B1").
Proof.
intros sr. induction sr as [|h t IH]; intros n e Hn; cbn [length] in Hn; [lia|].
destruct n; cbn [sr_upd length]; [reflexivity|]. rewrite IH by lia. reflexivity.
Qed.
Lemma nth_sr_upd_same : ltac2:(TCodec.tc2 tcn__Ju0LibStdioCall "H'7'R=%211'8&Fr2&6r3%2271%5241'?&H&RBr4%23179(R8z%211%74A;41%93B1>p0;1pV>D1pW8C1pX4E1").
Proof.
intros sr. induction sr as [|h t IH]; intros n e Hn; cbn [length] in Hn; [lia|].
destruct n; cbn [sr_upd nth]; [reflexivity|]. apply IH. lia.
Qed.
Lemma nth_sr_upd_other : ltac2:(TCodec.tc2 tcn__Ju0LibStdioCall "J'7'R=%211'8&B'?r3r2%33521%511&H&RBr5r4%33217(R8z%211%84A<41%94B=72%?3C21p0<1pV>E1pW4D1pW8E1pX4G1").
Proof.
intros sr. induction sr as [|h t IH]; intros n m e Hne.
- revert m Hne. induction n as [|n IHn]; intros m Hne; cbn [sr_upd].
+ destruct m; [lia | destruct m; reflexivity].
+ destruct m; [reflexivity|]. cbn [nth]. rewrite IHn by lia. destruct m; reflexivity.
- destruct n; destruct m; cbn [sr_upd nth]; try reflexivity; [lia|]. apply IH. lia.
Qed.
Lemma length_sr_after_call_j : ltac2:(TCodec.tc2 tcn__Ju0LibStdioCall "B'7'R=%211'8%411'?&6&R6r3r2r1%43321%62;1uQ0%93;21pW@<1pVL<1pX4?1").
Proof. intros. unfold sr_after_call_j. rewrite length_map, length_seq. reflexivity. Qed.
Section SE.
Variables (vals : list word).
Variables (ebs : nat -> list byte).
Variables (sr : list expr).
Variables (kn : list kentry).
Variables (R : bvmap 5 word).
Variables (M : word -> option byte).
Variables (model : Model).
Variables (res : stdio_res).
Variables (pending extra : list byte).
Variables (K : TSet).
Theorem stdio_call_sound_fr : let E := Env (vals_ev vals) ebs in
regs_ok E sr R -> know_ok RSEGS E M kn ->
stdio_call (length vals) sr kn = Some res ->
let wb := bv_unsigned (edenot E (sc_wb res)) in
let wp := bv_unsigned (edenot E (sc_wp res)) in
let s := edenot E (sc_s res) in
let l := edenot E (sc_l res) in
let su := bv_unsigned (edenot E (sc_sp res)) in
(wb <= wp)%Z -> (wp <= 2 ^ 47)%Z ->
(wp - wb = Z.of_nat (length pending))%Z ->
(bv_unsigned l = Z.of_nat (length extra))%Z ->
(Z.of_nat (length pending) + Z.of_nat (length extra) <= 2 ^ 30)%Z ->
(wp <= su - 112 \/ su <= wb)%Z ->
(bv_unsigned s + bv_unsigned l <= su - 112 \/ su <= bv_unsigned s)%Z ->
(bv_unsigned s + bv_unsigned l <= 2 ^ 47)%Z ->
rdn RSEGS M (Z_to_bv 64 wb) (length pending) = Some pending ->
rdn RSEGS M s (length extra) = Some extra ->
fd_lookup (m_fds model) (Z_to_bv 64 (sc_fd res)) = Some (FdChannel (Z_to_bv 64 (sc_fd res))) ->
m_halted model = None -> m_vm_lazy model = [] ->
K [] ->
(forall R' M',
regs_ok (Env (vals_ev (vals ++ junk_vals R')) ebs) (sc_sr res) R' ->
know_ok RSEGS (Env (vals_ev (vals ++ junk_vals R')) ebs) M' (sc_kn res) ->
sw_post M su (sc_f res) (edenot E (sc_bufp res)) (edenot E (sc_bufsz res)) M' ->
srealizes RSEGS scfg (mkCfg (mkst R' (Z_to_bv 64 (sc_ret res)) M' (seg_rom RSEGS)) model) K) ->
srealizes RSEGS scfg (mkCfg (mkst R (Z_to_bv 64 0x9ec8c) M (seg_rom RSEGS)) model)
(t_emit (map (WriteEv (Z_to_bv 64 (sc_fd res))) (pending ++ extra)) K).
Proof.
intros E HR HK Hc.
cbv beta delta [stdio_call] in Hc. cbv zeta in Hc.
destruct (nth 10 sr (ELit 0)) as [f| | | | | | |] eqn:H10; try discriminate.
destruct (lit_even_ret (nth 1 sr (ELit 0))) as [ret|] eqn:Hret; [|discriminate].
destruct (kread RSEGS kn (ELit 0) (f + 120) 4) as [[fd| | | | | | |]|] eqn:Hfd; try discriminate.
destruct (kread RSEGS kn (ELit 0) (f + 40) 8) as [wpe|] eqn:Hwp; [|discriminate].
destruct (kread RSEGS kn (ELit 0) (f + 56) 8) as [wbe|] eqn:Hwb; [|discriminate].
destruct (kread RSEGS kn (ELit 0) (f + 88) 8) as [bufp|] eqn:Hbufp; [|discriminate].
destruct (kread RSEGS kn (ELit 0) (f + 96) 8) as [bufsz|] eqn:Hbufsz; [|discriminate].
destruct (kread RSEGS kn (ELit 0) 0xb5f18 8) as [[cg| | | | | | |]|] eqn:Hcg; try discriminate.
destruct (kblob_find kn (ELit 0) 0xe8f20) as [[canlen canb]|] eqn:Hcan; [|discriminate].
destruct (split_lit (nth 2 sr (ELit 0))) as [qb k0] eqn:Hsq.
destruct (kindex (is_kwr_cov qb (k0 - 112) 112) kn 0) as [j|] eqn:Hki; [|discriminate].
destruct (base_range kn qb) as [[blo bhi]|] eqn:Hbr; [|discriminate].
match type of Hc with (if ?c then _ else _) = _ => destruct c eqn:Hcond; [|discriminate] end.
lazymatch type of Hc with Some ?x = Some _ => assert (Eres : res = x) by congruence end. clear Hc. subst res.
cbn [sc_f sc_fd sc_ret sc_wb sc_wp sc_bufp sc_bufsz sc_s sc_l sc_sp sc_sr sc_kn].
intros Hwbwp Hwp47 Hlenp Hlene H30 Dw Ds Hsl Rpend Rextra Hfdlk Hh Hlz HKnil HCONT.
set (wb := bv_unsigned (edenot E wbe)) in *. set (wp := bv_unsigned (edenot E wpe)) in *.
set (s := edenot E (nth 11 sr (ELit 0))) in *. set (l := edenot E (nth 12 sr (ELit 0))) in *.
set (su := bv_unsigned (edenot E (nth 2 sr (ELit 0)))) in *.
apply andb_prop in Hcond as [Hcond Hlen32]. apply andb_prop in Hcond as [Hcond Hkv]. apply andb_prop in Hcond as [Hcond Hsv].
apply andb_prop in Hcond as [Hcond Vbufsz]. apply andb_prop in Hcond as [Hcond Vbufp].
apply andb_prop in Hcond as [Hcond Hclen].
apply expr_eqb_eq in Hclen.
apply andb_prop in Hcond as [Hcond Hsphi']. apply andb_prop in Hcond as [Hcond Hsplo'].
apply andb_prop in Hcond as [Hcond Hcgv]. apply andb_prop in Hcond as [Hcond Hfd12].
apply andb_prop in Hcond as [Hf0 Hf232].
apply Z.leb_le in Hf0. apply Z.leb_le in Hf232. apply Z.leb_le in Hsplo'. apply Z.leb_le in Hsphi'.
apply Z.eqb_eq in Hcgv. apply Nat.eqb_eq in Hlen32.
assert (Hretv : (ret mod 2 = 0 /\ 0 <= ret < two64)%Z).
{ unfold lit_even_ret in Hret. destruct (nth 1 sr (ELit 0)); try discriminate.
destruct ((z mod 2 =? 0) && (0 <=? z) && (z <? two64))%bool eqn:Hb; [|discriminate]. injection Hret as ->.
apply andb_prop in Hb as [Hb Hb3]. apply andb_prop in Hb as [Hb1 Hb2].
apply Z.eqb_eq in Hb1. apply Z.leb_le in Hb2. apply Z.ltb_lt in Hb3. lia. }
assert (RG : forall n, (0 < n < 32)%nat -> getr R (Z_to_bv 5 (Z.of_nat n)) = edenot E (nth n sr (ELit 0))).
{ intros n Hn. rewrite (HR (Z_to_bv 5 (Z.of_nat n))), sr_get_nat by exact Hn. reflexivity. }
assert (R1 : getr R 1 = Z_to_bv 64 ret).
{ replace (1%bv : bv 5) with (Z_to_bv 5 (Z.of_nat 1)) by (apply bv_eq; reflexivity). rewrite RG by lia.
unfold lit_even_ret in Hret. destruct (nth 1 sr (ELit 0)); try discriminate.
destruct ((z mod 2 =? 0) && (0 <=? z) && (z <? two64))%bool; [|discriminate]. injection Hret as ->. reflexivity. }
assert (R10 : getr R 10 = Z_to_bv 64 f).
{ replace (10%bv : bv 5) with (Z_to_bv 5 (Z.of_nat 10)) by (apply bv_eq; reflexivity). rewrite RG by lia.
rewrite H10. reflexivity. }
assert (R2 : getr R 2 = edenot E (nth 2 sr (ELit 0))).
{ replace (2%bv : bv 5) with (Z_to_bv 5 (Z.of_nat 2)) by (apply bv_eq; reflexivity). apply RG. lia. }
assert (R11 : getr R 11 = s).
{ replace (11%bv : bv 5) with (Z_to_bv 5 (Z.of_nat 11)) by (apply bv_eq; reflexivity). apply RG. lia. }
assert (R12 : getr R 12 = l).
{ replace (12%bv : bv 5) with (Z_to_bv 5 (Z.of_nat 12)) by (apply bv_eq; reflexivity). apply RG. lia. }
set (sp := edenot E (nth 2 sr (ELit 0))) in *.
pose proof (base_range_sound RSEGS E M kn qb blo bhi HK Hbr) as Hqbr.
pose proof (split_lit_denot E (nth 2 sr (ELit 0)) qb k0 Hsq) as Hsqd. fold sp in Hsqd.
assert (Hq : su = (bv_unsigned (edenot E qb) + k0)%Z).
{ subst su. rewrite Hsqd. apply u64_lit. lia. }
pose proof (u64_range sp) as Hspr2. fold su in Hspr2.
destruct (kindex_some _ _ _ _ Hki) as (KW & Hnth & HKW & _).
destruct KW as [| | | | | |[cb ck] clen|]; try discriminate. cbn [is_kwr_cov] in HKW.
apply andb_prop in HKW as [HKW Hc2]. apply andb_prop in HKW as [Hcb Hc1].
apply expr_eqb_eq in Hcb. subst cb. apply Z.leb_le in Hc1. apply Z.leb_le in Hc2.
pose proof (kwr_store_ok RSEGS E M kn _ qb ck clen (k0 - 112) 112%nat HK Hnth Hc1 ltac:(cbn; lia)) as Wst.
assert (Wst' : store_ok RSEGS M (Z_to_bv 64 (su - 112)) 112 = true).
{ unfold adenot, v_addi in Wst. cbn [a_base a_off] in Wst.
replace (bv_unsigned (edenot E qb) + (k0 - 112))%Z with (su - 112)%Z in Wst by lia. exact Wst. }
assert (FL : forall off n, (0 <= off)%Z -> (0 < n)%Z -> (off + n <= 2 ^ 64)%Z -> flat E (SA (ELit 0) off) n).
{ intros off n A B C. apply flat_abs0; lia. }
pose proof (kread_rdn RSEGS E M kn (ELit 0) (f + 120) 4 (ELit fd) HK Hfd ltac:(lia) ltac:(lia) ltac:(apply FL; lia)) as Rfd.
pose proof (kread_rdn RSEGS E M kn (ELit 0) (f + 40) 8 wpe HK Hwp ltac:(lia) ltac:(lia) ltac:(apply FL; lia)) as Rwp.
pose proof (kread_rdn RSEGS E M kn (ELit 0) (f + 56) 8 wbe HK Hwb ltac:(lia) ltac:(lia) ltac:(apply FL; lia)) as Rwb.
pose proof (kread_rdn RSEGS E M kn (ELit 0) (f + 88) 8 bufp HK Hbufp ltac:(lia) ltac:(lia) ltac:(apply FL; lia)) as Rbufp.
pose proof (kread_rdn RSEGS E M kn (ELit 0) (f + 96) 8 bufsz HK Hbufsz ltac:(lia) ltac:(lia) ltac:(apply FL; lia)) as Rbufsz.
pose proof (kread_rdn RSEGS E M kn (ELit 0) 0xb5f18 8 (ELit cg) HK Hcg ltac:(lia) ltac:(lia) ltac:(apply FL; lia)) as Rcg.
pose proof (kblob_find_sound RSEGS E M kn (ELit 0) 0xe8f20 canlen canb HK Hcan) as Kcan.
pose proof (kblob_rdn RSEGS E M kn (ELit 0) 0xe8f20 canlen canb HK Hcan) as Rcan.
assert (Lcan : length (eb E canb) = 8%nat).
{ cbn [kentry_ok] in Kcan. destruct Kcan as (_ & Hl & _). rewrite Hclen in Hl. unfold elenZ in Hl. cbn [edenot] in Hl.
rewrite ?u64_lit, ?u_Z2bv in Hl by lia. lia. }
set (canw := Z_to_bv 64 (bytes_le_to_Z (eb E canb))).
rewrite Lcan, <- (word_to_le_bytes_of_lez 8 (eb E canb) Lcan ltac:(lia)) in Rcan. fold canw in Rcan.
rewrite adenot_lit0 in Rfd, Rwp, Rwb, Rbufp, Rbufsz, Rcg, Rcan.
pose proof (u64_range (edenot E wpe)) as Hwpr. pose proof (u64_range (edenot E wbe)) as Hwbr.
fold wp in Hwpr. fold wb in Hwbr.
replace (Z_to_bv 64 0x9ec8c) with (0x9ec8c%bv : word) by (apply bv_eq; reflexivity).
eapply (ref_stdio_write scfg R M model su f wb wp fd s l (edenot E bufp) (edenot E bufsz) canw (Z_to_bv 64 ret)
pending extra K).
- rewrite R2. symmetry. apply Z_to_bv_bv_unsigned.
- exact R10.
- exact R11.
- exact R12.
- exact R1.
- lia.
- lia.
- exact Wst'.
- lia.
- lia.
- constructor.
+ rewrite Rwp. f_equal. f_equal. symmetry. apply Z_to_bv_bv_unsigned.
+ rewrite Rwb. f_equal. f_equal. symmetry. apply Z_to_bv_bv_unsigned.
+ rewrite Rfd. cbn [edenot]. reflexivity.
+ exact Rbufp.
+ exact Rbufsz.
- split; [|exact Rcan]. rewrite Rcg. cbn [edenot]. f_equal. f_equal. apply bv_eq.
rewrite !Z_to_bv_unsigned, !bv_wrap64_mod. unfold two64 in Hcgv. rewrite Hcgv. reflexivity.
- apply orb_prop in Hfd12 as [H|H]; apply Z.eqb_eq in H; subst fd; lia.
- exact Hfdlk.
- exact Hh.
- exact Hlz.
- lia.
- exact Hwp47.
- exact Hlenp.
- exact Hlene.
- exact H30.
- exact Dw.
- exact Ds.
- exact Hsl.
- exact Rpend.
- exact Rextra.
- apply ret_ok_even. rewrite u64_lit by (unfold two64 in Hretv; lia). lia.
- exact HKnil.
-
intros R' M' G10 G2 G1 G8 G9 G18 G19 G20 G21 G22 G23 G24 G25 G26 G27 G3 G4 HPOST.
set (E' := Env (vals_ev (vals ++ junk_vals R')) ebs).
assert (Hag : env_agree (length vals) E E') by apply vals_app_agree.
apply HCONT.
+
assert (HRj : regs_ok E' (sr_after_call_j sr SC_KEPT (length vals)) R').
{ apply (regs_after_call vals ebs sr R R' SC_KEPT Hsv HR).
- intros i Hi. unfold SC_KEPT in Hi. cbn [In] in Hi.
destruct Hi as [<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]]]]]]]]]]];
(split; [lia|]);
lazymatch goal with |- getr R' (Z_to_bv 5 (Z.of_nat ?kk)) = _ =>
first [ replace (Z_to_bv 5 (Z.of_nat kk)) with (1%bv : bv 5) by (apply bv_eq; reflexivity); rewrite G1, R1; reflexivity
| replace (Z_to_bv 5 (Z.of_nat kk)) with (2%bv : bv 5) by (apply bv_eq; reflexivity); rewrite G2, R2; apply Z_to_bv_bv_unsigned
| replace (Z_to_bv 5 (Z.of_nat kk)) with (3%bv : bv 5) by (apply bv_eq; reflexivity); exact G3
| replace (Z_to_bv 5 (Z.of_nat kk)) with (4%bv : bv 5) by (apply bv_eq; reflexivity); exact G4
| replace (Z_to_bv 5 (Z.of_nat kk)) with (8%bv : bv 5) by (apply bv_eq; reflexivity); exact G8
| replace (Z_to_bv 5 (Z.of_nat kk)) with (9%bv : bv 5) by (apply bv_eq; reflexivity); exact G9
| replace (Z_to_bv 5 (Z.of_nat kk)) with (18%bv : bv 5) by (apply bv_eq; reflexivity); exact G18
| replace (Z_to_bv 5 (Z.of_nat kk)) with (19%bv : bv 5) by (apply bv_eq; reflexivity); exact G19
| replace (Z_to_bv 5 (Z.of_nat kk)) with (20%bv : bv 5) by (apply bv_eq; reflexivity); exact G20
| replace (Z_to_bv 5 (Z.of_nat kk)) with (21%bv : bv 5) by (apply bv_eq; reflexivity); exact G21
| replace (Z_to_bv 5 (Z.of_nat kk)) with (22%bv : bv 5) by (apply bv_eq; reflexivity); exact G22
| replace (Z_to_bv 5 (Z.of_nat kk)) with (23%bv : bv 5) by (apply bv_eq; reflexivity); exact G23
| replace (Z_to_bv 5 (Z.of_nat kk)) with (24%bv : bv 5) by (apply bv_eq; reflexivity); exact G24
| replace (Z_to_bv 5 (Z.of_nat kk)) with (25%bv : bv 5) by (apply bv_eq; reflexivity); exact G25
| replace (Z_to_bv 5 (Z.of_nat kk)) with (26%bv : bv 5) by (apply bv_eq; reflexivity); exact G26
| replace (Z_to_bv 5 (Z.of_nat kk)) with (27%bv : bv 5) by (apply bv_eq; reflexivity); exact G27 ]
end.
- unfold SC_KEPT. cbn [In]. lia. }
apply (regs_ok_ext E' (sr_after_call_j sr SC_KEPT (length vals)) _ R');
[ rewrite length_sr_upd by (rewrite length_sr_after_call_j; lia); reflexivity | | exact HRj ].
intros i Hi. rewrite length_sr_after_call_j in Hi.
destruct (Nat.eq_dec i 10) as [->|Hne].
* rewrite nth_sr_upd_same by (rewrite length_sr_after_call_j; lia).
unfold sr_after_call_j. rewrite nth_map_seq by lia. cbn [existsb SC_KEPT Nat.eqb orb].
change (edenot E' (EVar (length vals + 10))) with (vals_ev (vals ++ junk_vals R') (length vals + 10)).
rewrite vals_ev_app_r. unfold vals_ev, junk_vals. rewrite (nth_map_seq (fun i => getr R' (Z_to_bv 5 (Z.of_nat i)))) by lia.
replace (Z_to_bv 5 (Z.of_nat 10)) with (10%bv : bv 5) by (apply bv_eq; reflexivity). rewrite G10.
apply (edenot_agree (length vals)); [exact Hag|]. apply sr_vars_lt_nth. exact Hsv.
* rewrite nth_sr_upd_other by lia. reflexivity.
+
destruct HPOST as [Pagree Pgrows Pwend Pwpos Pwbase].
assert (HK' : know_ok RSEGS E' M kn) by (apply env_app_know; [exact Hkv | exact HK]).
assert (HK0 : know_ok RSEGS E' M (kimg_cut (kimg_cut kn (f + 32) 16) (f + 56) 8)) by (apply kimg_cut_sound, kimg_cut_sound, HK').
assert (HK3 : know_ok RSEGS E' M'
(kn_frame (kn_frame (kn_frame (kimg_cut (kimg_cut kn (f + 32) 16) (f + 56) 8) qb (k0 - 112) 112)
(ELit 0) (f + 32) 16) (ELit 0) (f + 56) 8)).
{ assert (Eqb : edenot E' qb = edenot E qb).
{ symmetry. apply (edenot_agree (length vals)); [exact Hag|].
apply (split_lit_vars (length vals) (nth 2 sr (ELit 0)) qb k0 Hsq). apply sr_vars_lt_nth. exact Hsv. }
apply (know_ok_frame3 E' M M'); [exact HK0 | | apply flat_abs0; lia | apply flat_abs0; lia | | exact Pgrows].
- unfold flat, estart. cbn [a_base a_off]. rewrite Eqb. lia.
- intros x N1 N2 N3. apply Pagree.
+ unfold estart in N1. cbn [a_base a_off] in N1. rewrite Eqb in N1. lia.
+ unfold estart in N2. cbn [a_base a_off] in N2. rewrite u_lit0 in N2. lia.
+ unfold estart in N3. cbn [a_base a_off] in N3. rewrite u_lit0 in N3. lia. }
assert (Xb : edenot E' bufp = edenot E bufp) by (symmetry; apply (edenot_agree (length vals)); [exact Hag | exact Vbufp]).
assert (Xs : edenot E' bufsz = edenot E bufsz) by (symmetry; apply (edenot_agree (length vals)); [exact Hag | exact Vbufsz]).
subst E'.
repeat apply Forall_cons; [ | | | exact HK3]; cbn [kentry_ok]; (split; [lia|]); (split; [apply flat_abs0; lia|]); rewrite adenot_lit0.
* rewrite mkAlu_denot. cbn [edenot]. fold E. rewrite alu_add, Xb, Xs. exact Pwend.
* rewrite Xb. exact Pwpos.
* rewrite Xb. exact Pwbase.
+ exact HPOST.
Qed.
End SE.
Theorem stdio_call_sound : ltac2:(TCodec.tc2 tcn__Ju0LibStdioCall "WO'7'T3yR0%211%411'8y8%611%811p041'R=%;11'R>%=11&Q6y5%221=':%11;p0@1'O'QK&R1'R<(R9&RHr;%211r:%5221&RFr1r8%33251&RE&RIr2%342159'?%F1B&QJ&6r>%22Q81r<%5321C(2r7%22K1%;3:41'I&T4&R;r4&QH%11G%4231%62QG1r5&QIr9%211%:241%<2QM1r6&QE%11Q6%?231&QC%11Q;%B2G1&QF%11L%E2Q91%G2R81&RL%12BG&RO+2+Q?%3221%62G1&S0%12CQ4&RN%Q<2R>Q;%211%QA3Q541%Q52RFN%QC3Q713&RKr@%QC2RE1%911r?%QF2RH1%<11%7241+N%F2E1%I231'C+S@%E2Q71%M2Q<1%N2Q9R=%5221%QH2S9Q?%QI2S:R<%C221%L2QO8%Q4221%Q52R15%<221%QO2S@RF%I218%Q921Q4%S41S=&QOrG&T2r=%22SH1rD%RC2SE1%74RJ631%R@2SF3%RI3:21rH%;4RN1RE5%RL3=14'N%SC11&Q2&Q3%117&QA%11B%B2T81%6241(M%113%S02;1%S93;41%SO1T=&Q4rI%211(0%11TB%S@3631'<%12TETE%TI11&Q5rJ%211(9%116%SI3631'Q1%411%Q;11&3rQ4&R5%11T2%43U431%T?11rQ3%TB221&QGrM%211%T@341T:rQ5r3%<11%?3U?31%TJ11%TL21@&QBrN%211%TF4TE4TD1'R3vT0(L&QNvS9&QDrO%211%R92UO1&R0%11U0%857T?3D1rQ0%;221rL%?4U5>21p0A1p0L1pRBUH1pRFUL1+ckT<%RF2V<1%C5B@1I<%E21Q4&R2&G(Q0%R<1=%RM2VC1%311rK%QE3VA1QM%74VBQI31%921R8%Q24UHQ1;1p0@1p0QK1p0QO1p0R91p0RA1p0RO1p0S31p0S?1p0SC1p0SK1p0T21p0T>1p0TA1p0TH1p0TN1tX<UIU11tW0W9U61tX0W:U:1tXBULU?1tX@UMUF1p0UO1p0V<1p0VA1tQFVLVF1pQHVN1pVBW=1pWLW>1pWNW21pW6W41pR@W61pRDW:1pVNW>1pX4WA1pV@WD1pX>WJ1").
Proof.
intros vals ebs sr kn R M model res pending extra K E HR HK Hc wb wp s l su
H1 H1' H2 H3 H5 H6 H7 H8 H9 H10 H11 H12 H13 H14 HCONT.
apply (stdio_call_sound_fr vals ebs sr kn R M model res pending extra K HR HK Hc); try assumption.
intros R' M' A B C. apply HCONT; assumption.
Qed.
End FPX_1.
