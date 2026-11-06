(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require BvWfKernel.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.LinuxProcessSem.Checks Require Import ExecutableSpecs.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.jsoncons.fuzz_ubjson_parser_max.images Require Import Ubsan.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import RunEnv
PropExec CatExec CatSim SeqExec StoreOk SimInv ExitSim ShapeAlg ShapeLaws Nodes
MmapSim AllocSim FileSim AgentLib SpecConsts DivergeSim SpinAlg SpinAlgX
SymExec SymExec2 SymExec2Sound SymRun SymDrive SymDriveX SymDriveH4 LibKnowFrame
Spec LibWritev RefNodes RefMemcpyLib RefReadLib RefPrintfLib Ju0Startup Ju0MainEntry Hoare MemSplit
Ju0ExitBase Ju0StdioDefs Ju0Exit Ju0LibStdioCall
HeapIface DrvKit Ju0Drv_defs Ju0DrvLib Ju0DrvA Ju0DrvB Ju0DrvG_defs Ju0DrvG Ju0DrvC_defs.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.
Import SX2. Import SX2S.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require TCodec.
Ltac2 tcn__Ju0DrvC () := ([""; "Corelib.Init.Datatypes."; "Corelib.Init.Logic."; "Corelib.Init.Peano."; "Corelib.Lists.ListDef."; "Corelib.Numbers.BinNums."; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics."; "LinuxProcessSemantics.LinuxProcessSem.State."; "LinuxProcessSemantics.Riscv.Instr."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.HeapIface."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.Ju0DrvC.FPX_1.DrvC."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.Ju0DrvC_defs."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.Ju0DrvG_defs."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.Ju0DrvLib."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.Ju0MainEntry."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.Ju0StdioDefs."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PropExec."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.ShapeAlg."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.Spec."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.SymExec2.SX2."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.SymExec2Sound.SX2S."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.SymRun."; "OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.Ubsan.M."; "Stdlib.Lists.List."; "Stdlib.ZArith.BinInt.Z."; "stdpp.bitvector.definitions."], [["0A"; "0A1"; "0CAP"; "1None"; "1Some"; "1bool"; "1cons"; "1length"; "1list"; "1nat"; "1nil"; "1option"; "1prod"; "2and"; "2eq"; "3le"]; ["3lt"; "4nth"; "5Z"; "0ENVb"; "0HI"; "0KT"; "0LB"; "0LEN"; "6word_to_le_bytes"; "7FdChannel"; "7FdEntry"; "7Model"; "7VmMaps"; "7event"; "7fd_lookup"; "7m_fds"]; ["7m_vmmaps"; "8ALU_ADD"; "8BC_LTU"; "0M"; "0M'"; "9credit"; "9hi_heap"; "9model_but_vm"; ":B0"; ":B1"; ":B2"; ":CFG"; ":err_tail_stmt"; ":target_k"; ";cfglen_x"; ";knGL"]; [";knIo0"; ";knIs0"; ";srIo0"; ";srIs0"; "<knG"; "=hz"; ">auxvp"; ">rnd"; "?sw_post"; "@rdn"; "ATSet"; "Bmsg_overrun"; "Bmsg_short"; "Bt_die"; "CEAlu"; "CELit"]; ["CEVar"; "CKRange"; "CKWord"; "CSA"; "CSCBr"; "Dkentry_ok"; "Dknow_ok"; "Dsc_denot"; "Evals_ev"; "Floaded_segments"; "GIn"; "Hadd"; "Hle"; "Hlt"; "Hltb"; "Hof_nat"]; ["Hpow"; "Hsub"; "Hto_nat"; "0VM"; "0a0s"; "0above"; "0bufp"; "0bufsz"; "0close_kg"; "0cr"; "0data"; "0envv"; "0fdata"; "0fs0"; "0hi"; "0i"]; ["0j"; "0k"; "0lo"; "0m'"; "0model2"; "0path"; "0sp0"; "IZ_to_bv"; "Ibv"; "Ibv_unsigned"; "0su"; "0t"; "0v"; "0vals"; "0x"]]).
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Local Ltac lia := first [ solve [ try (match goal with H : (length _ <= S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S _)))))))))))))))))))))))))))))))))%nat |- _ => clear dependent H end); Lia.lia ] | Lia.lia ].
Tactic Notation "run_block" constr(scr) constr(NX) := run_block_gen FUEL STOPS scr NX false.
Tactic Notation "run_block_keep" constr(scr) constr(NX) := run_block_gen FUEL STOPS scr NX true.
Tactic Notation "run_blockH" constr(scr) constr(NX) := run_block_gen FUEL STOPS_H scr NX false.
Tactic Notation "run_blockH_keep" constr(scr) constr(NX) := run_block_gen FUEL STOPS_H scr NX true.
Section FPX_1. Context {fx : PropExec.FPState}.
Variable scfg : SpuriousCfg.
#[using="Type"] Lemma msg_short_img : ltac2:(TCodec.tc2 tcn__Ju0DrvC "H'>';'8'S8y8%211%411%611&QI&R9yR0%811(3%118q031&S7+R\b5%2271uO%;4:521(4&QL%22@1%G3@41").
Proof. vm_compute. reflexivity. Qed.
#[using="Type"] Lemma msg_overrun_img : ltac2:(TCodec.tc2 tcn__Ju0DrvC "H'>';'8'S8y8%211%411%611&QI&R9yR0%811(3%118q031&S7+RTUE%2271uO%;4:521(4&QK%22@1%G3@41").
Proof. vm_compute. reflexivity. Qed.
#[using="Type"] Lemma msg_short_len : ltac2:(TCodec.tc2 tcn__Ju0DrvC ":'>'9&7'S8y8%211&QL%5221uO%93821"). Proof. reflexivity. Qed.
#[using="Type"] Lemma msg_overrun_len : ltac2:(TCodec.tc2 tcn__Ju0DrvC ":'>'9&7'S8y8%211&QK%5221uO%93821"). Proof. reflexivity. Qed.
#[using="Type"] Lemma w2le1_byte : ltac2:(TCodec.tc2 tcn__Ju0DrvC "E'S8y8%211'>'8%113&Hu1&S7yR0&S9r1%22;1%5241%8271(6(:%11?%33@71%@3>51pVNB1").
Proof.
intros x. pose proof (bv_unsigned_in_range _ x) as Hx. change (bv_modulus 8) with 256%Z in Hx.
unfold word_to_le_bytes. cbn [Z_to_le_bytes]. f_equal.
rewrite u_small by lia. apply Z_to_bv_bv_unsigned.
Qed.
#[using="Type"] Lemma content_byte : ltac2:(TCodec.tc2 tcn__Ju0DrvC "R7'S8yR0%211';y8%511%311p051'B'8%115'9'>%:13&QI&R9r4&S7r3%22B1&7r2%22A1%948741(4%12?4%>3=31&@%82G:%2281&R<zr5%3221&R=&R;r6&R?%B2Q16%211%5241&R@+2+R0%3221%;251r8r7%;1@%>221%Q12QA1u1%Q64Q5621&H&S9&A%Q72QDI%24QDIE1%42QF1%Q:2QJ1%7291%Q52QC1%QB3QA:1p0B1p0O1p0Q41p0Q81pV2QH1pUFQJ1p2QM1pR8QO1").
Proof.
intros M A data j Hc Hj HA HA2.
pose proof (rdn_nth RSEGS M (length data) _ data j Hc Hj) as H.
rewrite w_add_nat in H. rewrite u_small in H by lia. rewrite w2le1_byte. exact H.
Qed.
Section DrvC.
Context {RE : RunEnv}.
Variable L : heap_layout.
Variable HI : heap_iface.
Hypothesis HIok : heap_iface_ok L scfg HI.
Variable sp0 : word.
Variables a0s path : list byte.
Variable envv : list (list byte).
Variable uid : word.
Variable hw : word.
Variable rdraw : EntryDraw.
Variable tid : word.
Variable regs0 : bvmap 5 word.
Variable mem0 : word -> option byte.
Variable VM0 : VmMaps.
Variable fs0 : Fs.
Variable stdin0 : InputStream.
Variable fdata : list byte.
Variable cr0 : credit.
Hypothesis Hva : valid_argv [a0s; path].
Hypothesis Hve : valid_envp envv.
Hypothesis Hvsp : valid_sp sp0.
Hypothesis Htid : (0 < bv_unsigned tid < 2 ^ 22)%Z.
Hypothesis ME : main_entry sp0 [a0s; path] envv uid hw rdraw tid regs0 mem0.
Hypothesis Hfile : fs_lookup fs0 path = Some fdata.
Hypothesis Hplen : (length path <= 4095)%nat.
Hypothesis DL : drv_layout L sp0.
Variable CAP : Z.
Hypothesis HCAP : (65536 <= CAP <= 67108864)%Z.
Variable crC : credit.
Hypothesis HLEN : (Z.of_nat (length fdata) < CAP)%Z.
Let Hsp : (0x7fff80000000 <= bv_unsigned sp0 <= 0x800000000000)%Z := conj (proj1 Hvsp) (proj1 (proj2 Hvsp)).
Let Hal : (bv_unsigned sp0 mod 16 = 0)%Z := proj2 (proj2 Hvsp).
Let LEN : Z := Z.of_nat (length fdata).
Let ENVb (vals : list word) : env := ENV a0s path hw rdraw fdata vals.
Let above (M : word -> option byte) : Prop := above_sp0 sp0 mem0 M.
Let model2 (VM : VmMaps) : Model := model2 tid fs0 stdin0 VM.
Definition B0 : Z := bv_unsigned (nth 0 fdata (Z_to_bv 8 0)).
Definition B1 : Z := bv_unsigned (nth 1 fdata (Z_to_bv 8 0)).
Definition B2 : Z := bv_unsigned (nth 2 fdata (Z_to_bv 8 0)).
Definition CFG : Z := ((B0 + 256 * B1) mod 32768)%Z.
Definition PL : Z := (LEN - 6 - CFG)%Z.
#[using="LEN"] Lemma B0_range : ltac2:(TCodec.tc2 tcn__Ju0DrvC "9'=&R<z&Q8%3221&R=+X0%2241%8241").
Proof. clear Htid Hplen HLEN Hsp Hal. unfold B0. pose proof (bv_unsigned_in_range _ (nth 0 fdata (Z_to_bv 8 0))) as H. change (bv_modulus 8) with 256%Z in H. lia. Qed.
#[using="LEN"] Lemma B1_range : ltac2:(TCodec.tc2 tcn__Ju0DrvC "9'=&R<z&Q9%3221&R=+X0%2241%8241").
Proof. clear Htid Hplen HLEN Hsp Hal. unfold B1. pose proof (bv_unsigned_in_range _ (nth 1 fdata (Z_to_bv 8 0))) as H. change (bv_modulus 8) with 256%Z in H. lia. Qed.
#[using="LEN"] Lemma B2_range : ltac2:(TCodec.tc2 tcn__Ju0DrvC "9'=&R<z&Q:%3221&R=+X0%2241%8241").
Proof. clear Htid Hplen HLEN Hsp Hal. unfold B2. pose proof (bv_unsigned_in_range _ (nth 2 fdata (Z_to_bv 8 0))) as H. change (bv_modulus 8) with 256%Z in H. lia. Qed.
#[using="LEN"] Lemma CFG_range : ltac2:(TCodec.tc2 tcn__Ju0DrvC "9'=&R<z&Q;%3221&R=+QPP0%2241%8241").
Proof. clear Htid Hplen HLEN Hsp Hal. unfold CFG. apply Z.mod_pos_bound. lia. Qed.
Let close_kg := close_kg scfg L HI sp0 a0s path envv hw rdraw tid mem0 fs0 stdin0 fdata CAP crC.
Definition target_k (KT : TSet) : Prop :=
forall vals R M VM (A1 : Z),
length vals = 81%nat -> vals_ev vals 0 = sp0 -> vals_ev vals 48 = Z_to_bv 64 A1 -> vals_ev vals 70 = Z_to_bv 64 LEN ->
vals_ev vals 1 = p0 sp0 a0s path envv -> vals_ev vals 2 = p1 sp0 a0s path envv ->
vals_ev vals 3 = auxvp sp0 a0s path envv -> vals_ev vals 4 = rnd sp0 a0s path envv -> vals_ev vals 5 = tid ->
vals_ev vals 71 = Z_to_bv 64 B0 -> vals_ev vals 72 = Z_to_bv 64 B1 -> vals_ev vals 73 = Z_to_bv 64 CFG ->
vals_ev vals 79 = Z_to_bv 64 PL -> vals_ev vals 80 = Z_to_bv 64 B2 ->
regs_ok (ENVb vals) srT0 R -> know_ok RSEGS (ENVb vals) M knT0 ->
above M -> block_range L A1 CAP ->
rdn RSEGS M (Z_to_bv 64 A1) (length fdata) = Some fdata ->
hi_heap HI [(A1, CAP)] crC M VM ->
srealizes RSEGS scfg (mkCfg (mkst R (Z_to_bv 64 0x340ec) M (seg_rom RSEGS)) (model2 VM)) KT.
#[using="sp0 Hvsp Hplen CAP HCAP HLEN Hsp"] Lemma ltu_hdr_sc : ltac2:(TCodec.tc2 tcn__Ju0DrvC "R0'8'S8yR0%211%411';y8%611%311p061'5'>&R8r3uR6%3221&S7vG%22@1%83@41r4uR7%:221&Q8%82F1%>3F31r5uR8%@221&Q9%>2L1%D3L31&R>&R;&Q;+6%3221%52D1%K3L1B&R7&R9r6vCr7%211(R4(Q2(R0%11Q2(QN(Q1&Q>(QO%11B%53431%:4M971%A4@?<1p0C1p0K1p0Q21p0Q91pVHQC1pR8QE1pVLQK1").
Proof.
intros vals M t P70 P71 P72 Ht. pose proof B0_range as R0. pose proof B1_range as R1. pose proof CFG_range as RC.
cbn [sc_denot branch_taken].
change (edenot (ENVb vals) (EAlu ALU_ADD cfglen_x (ELit 6))) with (alu64 ALU_ADD (edenot (ENVb vals) cfglen_x) (Z_to_bv 64 6)).
change (edenot (ENVb vals) (EVar 70)) with (vals_ev vals 70).
unfold ENVb, ENV. rewrite cfglen_x_cfgF, P70, P71, P72, cfgF_val by lia. fold CFG.
rewrite alu_add_Z. unfold bv_ltu. rewrite !u_small by lia. exact Ht.
Qed.
#[using="Hvsp Hplen HCAP HLEN Hsp LEN"] Lemma kbyte48 : ltac2:(TCodec.tc2 tcn__Ju0DrvC "RB'8'S8yR0%211%411';y8%611%311p061'B'9'>&R8r5uQ@%3221&S7r3%22A1%83A41&QEvS6r4v2%43321%J1C%F11&QI&R9r6%>2MA&7vRL%22K1%746541(4%12;4%J3;31&R<z%221K&@&RB%11>%321;r:%Q221A&S9&Ar7%811%Q32Q><%44Q>2D1%62Q@1%Q62QE1%Q<3QE91&R5vCr;%211(R2(R3(R0%11QAr8%4221u1%51B%83321%=4Q9:H1p0?1p0K1p0Q01p0Q41p0QB1p0QH1pVJR21pV4R41p4R51pR8R71pVLR=1").
Proof.
intros vals M A1 k v P48 (Z1 & Z2 & Z3) HC Hk Hkl Pv. pose proof Hsp as Hsp'.
cbn [kentry_ok]. split; [lia|]. split.
- apply flat_intro; cbn [edenot ev ENVb ENV]; rewrite ?P48, ?u_small by lia; lia.
- unfold adenot, v_addi. cbn [a_base a_off edenot ev ENVb ENV]. rewrite P48, Pv, u_small by lia.
replace (A1 + k)%Z with (A1 + Z.of_nat (Z.to_nat k))%Z by lia. apply content_byte; [exact HC | exact Hkl | lia | lia].
Qed.
#[using="sp0 Hplen LEN"] Lemma krange_lit : ltac2:(TCodec.tc2 tcn__Ju0DrvC "QI'8'S8yR0%211%411';y8%611%311p061'9'B'>&R8r6r4%3221&S7r3%22A1%83A41'=&R<z%2219&R=&R@+2+R0%3221%52?1%:271r5%;2B1%<22@%>221&R5&R9vCr9%211r8(R1(R0r7%211%431>O%;4:761p0=1p0B1p0N1pUNQ81pV6Q91pVNQ:1pVJQ<1pR8Q>1pVLQD1").
Proof. intros vals M v x lo hi Pv Hx Hr. cbn [kentry_ok edenot ev ENVb ENV]. rewrite Pv, u_small by lia. lia. Qed.
#[using="uid hw rdraw Hva Hve Hvsp Hplen"] Lemma hiv_facts' : ltac2:(TCodec.tc2 tcn__Ju0DrvC "QF'8'S8yR0%211%411'>&R8r1u3%3221&QFvS6vRDvS5vRK%544321%;3=71r2u4%=221&QG%14:987%A3C31'9&R:(6(:%114%335:1%436E1%637G1'=&R<&S9%12Q0Gr5%N21C%42Q31%6241&R;&R@+2+D%3221%5271+R0%6251%?231%A2:1p0C1pV0K1p0M1p0Q41pVLQA1").
Proof. intros vals P3 P4 i Hi. exact (hiv_facts sp0 a0s path envv uid hw rdraw Hva Hve Hvsp Hplen vals P3 P4 i Hi). Qed.
#[using="Type"] Lemma m2_but : ltac2:(TCodec.tc2 tcn__Ju0DrvC "@'L'K&Q7vS4r2%211r1%5221'>&Q0%116%811%43;81p061pV8=1pU8?1").
Proof. intros VM m' H. exact H. Qed.
#[using="Type"] Lemma m2_fd2 : ltac2:(TCodec.tc2 tcn__Ju0DrvC "F'L'>';'J%211&N&OvS4r1%211%411&S7yR0+2%3221%:251(4(I%114%32@1%C3@51pU8E1").
Proof. intros. reflexivity. Qed.
#[using="scfg L HIok path fdata Hvsp Hplen DL Hsp LEN"] Lemma heap_sw_post : ltac2:(TCodec.tc2 tcn__Ju0DrvC "QH'8'<'B%2211%411&Q5'S8yR0%211';y8%511%311p051'L&Q6vDr8r7r6r5%6554321'QHr4+flQ@r3r2%56943217&R<&R;&RA&S9vS6%22J1+XPPP0%5221+S@%8221%:21B%;2D6r<r;r9%L5K32J1p051p071p0C1p0J1pU@Q81pU>Q91pVFQ@1pR:Q61pU8Q61pR8Q81pUDQA1pQ>QC1").
Proof.
intros LB cr M VM M' su bufp bufsz HH HP Hlo Hhi.
pose proof (dl_ro L sp0 DL) as RO. pose proof (dl_static L sp0 DL) as STA. pose proof (dl_sptop L sp0 DL) as TOP.
pose proof (dl_img_lo L sp0 DL) as IL. pose proof (dl_img_hi L sp0 DL) as IH.
apply (hio_frame L scfg HI HIok LB cr M M' VM HH).
- intros a Ha Hpriv. apply (swp_agree _ _ _ _ _ _ HP); rewrite u_small by lia.
+ intros Hin. destruct Hpriv as [[A _]|A]; [rewrite TOP in A; lia|]. apply RO in A. lia.
+ intros Hin. destruct Hpriv as [[_ [_ A]]|A]; [| apply RO in A; lia].
apply A. rewrite IL, IH. split; [lia|]. intros Hs. apply STA in Hs. lia.
+ intros Hin. destruct Hpriv as [[_ [_ A]]|A]; [| apply RO in A; lia].
apply A. rewrite IL, IH. split; [lia|]. intros Hs. apply STA in Hs. lia.
- exact (swp_grows _ _ _ _ _ _ HP).
Qed.
#[using="path fdata Hvsp Hplen Hsp LEN"] Lemma above_sw_post : ltac2:(TCodec.tc2 tcn__Ju0DrvC "Q2'S8yR0%211';y8%511%311p051'BvREr5%211'QHr6r4+flQ@r3r2%66543218&R<&S9vS6%22E1%42=1r7%@11p031p091p0A1pU@K1pU>L1pVFG1pR:I1pR8J1").
Proof.
intros M M' su bufp bufsz HA HP Hhi a Ha. rewrite (swp_agree _ _ _ _ _ _ HP); [apply HA; exact Ha | lia | lia | lia].
Qed.
Definition err_tail_stmt (sr : list expr) (kn : list kentry) (NV : nat) : Prop :=
forall vals R M VM (A1 : Z),
length vals = NV -> vals_ev vals 0 = sp0 -> vals_ev vals 48 = Z_to_bv 64 A1 ->
vals_ev vals 3 = auxvp sp0 a0s path envv -> vals_ev vals 4 = rnd sp0 a0s path envv -> vals_ev vals 5 = tid ->
regs_ok (ENVb vals) sr R -> know_ok RSEGS (ENVb vals) M kn ->
block_range L A1 CAP -> hi_heap HI [(A1, CAP)] crC M VM ->
srealizes RSEGS scfg (mkCfg (mkst R (Z_to_bv 64 0x9f524) M (seg_rom RSEGS)) (model2 VM))
(t_exit (exit_code 2) fs0).
Ltac close_exit2 HR HK P0 P5 :=
lazymatch type of HK with know_ok ?segs ?E ?M ?kn =>
lazymatch goal with |- srealizes _ _ (mkCfg _ ?model) _ =>
apply (srz_conseq segs scfg _ (t_emit (W 1 []) (t_exit (bv_and (Z_to_bv 64 2) (Z_to_bv 64 255)) (m_fs model))));
[ | cbn [W map];
replace (bv_and (Z_to_bv 64 2) (Z_to_bv 64 255)) with (exit_code 2) by (apply bv_eq; reflexivity);
apply t_eq_sym; apply t_emit_nil_exit ];
apply ref_exit_Z;
let Ktid := fresh "Ktid" in
pose proof (know_nth segs _ _ kn ltac:(let i := kidx kn (is_krange (EVar 5)) in exact i) _ HK eq_refl)
as Ktid; cbn [kentry_ok edenot ev ENVb ENV] in Ktid; rewrite P5 in Ktid;
lazymatch type of HR with regs_ok _ _ ?Rc =>
exists (Z_to_bv 64 (bv_unsigned sp0 - 48)), (Z_to_bv 64 0xc8cb0), (bv_unsigned tid),
(Z_to_bv 64 955544), (Z_to_bv 64 0);
split; [|split; [reflexivity|split; [reflexivity|]]];
[ constructor;
[ regv HR (2 : reg); rewrite edenot_add_lit; unfold adenot, v_addi; cbn [a_base a_off edenot ev ENVb ENV];
rewrite P0; f_equal; lia
| regv HR (4 : reg); reflexivity
| regv HR (10 : reg); reflexivity
| rewrite u_small by lia; lia
| rewrite u_small by lia; lia
| rewrite u_small by lia;
let Hst := fresh "Hst" in
pose proof (kwr_store_ok segs E _ kn ltac:(let i := kidx kn (is_kwr_cov (EVar 0) (-192) 144) in exact i)
_ _ _ (-192) 144 HK eq_refl ltac:(lia) ltac:(cbn; lia)) as Hst;
unfold adenot, v_addi in Hst; cbn [a_base a_off edenot ev ENVb ENV] in Hst; rewrite P0 in Hst;
replace (bv_unsigned sp0 - 48 - 144)%Z with (bv_unsigned sp0 + -192)%Z by lia; exact Hst
| lit_u; lia
| lit_u; lia
| lia
| lit_u; change (822448 - 168)%Z with 0xc8c08%Z;
let Htc := fresh "Htc" in
krd HK 0xc8c08%Z 4%nat Htc; rewrite Htc; cbn [ev ENVb ENV]; rewrite P5;
rewrite ext_val_zx_id by (change (2 ^ (8 * Z.of_nat 4))%Z with 4294967296%Z; lia);
rewrite Z_to_bv_bv_unsigned; reflexivity
| krd_solve HK | krd_solve HK | krd_solve HK | krd_solve HK | krd_solve HK | krd_solve HK | krd_solve HK | (exists 0%nat; split; krd_solve HK) | krd_solve HK
| repeat split; krd_solve HK
| repeat split; krd_solve HK ]
| left; split; [reflexivity|]; exists (Z_to_bv 64 0), (Z_to_bv 64 0); repeat split; krd_solve HK ]
end end end.
Ltac err_tail_tac NV :=
let NV2 := eval vm_compute in (NV + 32)%nat in
intros vals R M VM A1 HL P0 P48 P3 P4 P5 HR HK HBR HH;
pose proof Hsp as Hsp'; pose proof Hal as Hal';
pose proof (hiv_facts' vals P3 P4) as HIV;
run_block_keep scr0 NV;
lazymatch goal with EQM : ?m0 = mem_denot _ _ _ |- _ => cbn [mem_denot] in EQM; subst m0 end;
lazymatch goal with |- srealizes _ _ (mkCfg (mkst ?Rc _ ?Mc _) _) _ =>
lazymatch type of HR with regs_ok _ ?sr _ =>
lazymatch type of HK with know_ok _ _ _ ?kn =>
eapply (free_site scfg L HI HIok sp0 Hsp' Hal' DL vals _ sr kn Rc Mc (model2 VM) [(A1, CAP)] crC
A1 CAP (-128) [] [] 0x34018);
[ exact HR | exact HK
| rewrite HL; vm_compute; reflexivity | rewrite HL; vm_compute; reflexivity | rewrite HL; lia
| exact P0 | exact HIV | vm_compute; reflexivity
| regv HR (2 : reg); cbn [edenot ev ENVb ENV]; rewrite P0; apply alu_add_w_lit
| lia | reflexivity
| left; reflexivity
| regv HR (10 : reg); cbn [edenot ev ENVb ENV]; exact P48
| regv HR (4 : reg); reflexivity
| regv HR (1 : reg); reflexivity
| lia | reflexivity
| exact HH | reflexivity | reflexivity | reflexivity
| intros i nb Hf; discriminate
| intros v b Hf; discriminate
| apply t_exit_has_nil
| ]
end end end;
clear HR HK;
let R' := fresh "R" in let M' := fresh "M" in let model' := fresh "model" in
let HL' := fresh "HL" in let HBUT := fresh "HBUT" in let HH' := fresh "HH" in let HAB := fresh "HAB" in let HBLK := fresh "HBLK" in let HIMG := fresh "HIMG" in
let vals' := fresh "vals" in let E' := fresh "E" in
intros R' M' model' vals' E' HL' HR HK HH' HBUT HAB HBLK HIMG; subst vals' E';
rewrite (m2_but _ _ HBUT);
let P0' := fresh "P0" in let P5' := fresh "P5" in
assert (P0' : vals_ev (vals ++ junk_vals R') 0 = sp0) by (rewrite vals_ev_app_l by (rewrite HL; lia); exact P0);
assert (P5' : vals_ev (vals ++ junk_vals R') 5 = tid) by (rewrite vals_ev_app_l by (rewrite HL; lia); exact P5);
run_block scr0 NV2;
close_exit2 HR HK P0' P5'.
#[using="HIok uid Hva Hve Hvsp Htid Hplen DL Hsp Hal LEN"] Lemma err_tail_short : ltac2:(TCodec.tc2 tcn__Ju0DrvC "5&Q<&QC&QAuS7%43321").
Proof. unfold err_tail_stmt. err_tail_tac 103%nat. Qed.
#[using="HIok uid Hva Hve Hvsp Htid Hplen DL Hsp Hal LEN"] Lemma err_tail_overrun : ltac2:(TCodec.tc2 tcn__Ju0DrvC "5&Q<&QB&Q@uS9%43321").
Proof. unfold err_tail_stmt. err_tail_tac 105%nat. Qed.
Ltac stdio_then_tail vals A1 NV res msg msg_img msg_addr TAIL HL P0 P48 P3 P4 P5 HR HK HH HBR :=
lazymatch type of HK with know_ok _ _ ?Mc ?kn =>
lazymatch type of HR with regs_ok _ ?sr ?Rc =>
lazymatch goal with |- srealizes _ _ (mkCfg _ (?model2f ?VMc)) _ =>
unfold t_die, W;
let HSC := fresh "HSC" in let Hsc := fresh "Hsc" in
assert (HSC : stdio_call NV sr kn = Some res) by (vm_compute; reflexivity);
pose proof (stdio_call_sound_fr scfg vals _ sr kn Rc Mc (model2 VMc) res [] msg
(t_exit (exit_code 2) fs0) HR HK (eq_trans (f_equal (fun n => stdio_call n sr kn) HL) HSC)) as Hsc;
cbn [sc_f sc_fd sc_ret sc_wb sc_wp sc_bufp sc_bufsz sc_s sc_l sc_sp sc_sr sc_kn res length app Z.of_nat] in Hsc;
apply Hsc; clear Hsc HSC;
[ cbn [edenot]; lia
| cbn [edenot]; rewrite ?u_small by lia; lia
| cbn [edenot]; lia
| cbn [edenot]; lit_u; reflexivity
| replace (Z.of_nat (@length byte msg)) with 31%Z by reflexivity; cbn [Z.of_nat]; lia
| left; rewrite edenot_add_lit; unfold adenot, v_addi; cbn [a_base a_off edenot ev ENVb ENV]; rewrite P0;
rewrite ?u_small by lia; lia
| left; rewrite edenot_add_lit; unfold adenot, v_addi; cbn [a_base a_off edenot ev ENVb ENV]; rewrite P0;
rewrite ?u_small by lia; lia
| cbn [edenot]; rewrite ?u_small by lia; lia
| reflexivity
| cbn [edenot]; replace (@length byte msg) with 31%nat by reflexivity;
rewrite (kimg_rdn RSEGS _ _ kn ltac:(let i := kidx kn (is_kimg_cov msg_addr 31) in exact i)
_ _ msg_addr 31 HK eq_refl) by (cbn; lia);
apply msg_img
| apply m2_fd2
| reflexivity
| reflexivity
| apply t_exit_has_nil
| clear HR HK;
let R' := fresh "R" in let M' := fresh "M" in let HR' := fresh "HR" in let HK' := fresh "HK" in let HP := fresh "HP" in
intros R' M' HR' HK' HP;
rewrite edenot_add_lit in HP; unfold adenot, v_addi in HP; cbn [a_base a_off edenot ev ENVb ENV] in HP; rewrite P0 in HP;
apply (TAIL (vals ++ junk_vals R') R' M' VMc A1);
[ rewrite length_app, junk_vals_length, HL; reflexivity
| rewrite vals_ev_app_l by (rewrite HL; lia); exact P0
| rewrite vals_ev_app_l by (rewrite HL; lia); exact P48
| rewrite vals_ev_app_l by (rewrite HL; lia); exact P3
| rewrite vals_ev_app_l by (rewrite HL; lia); exact P4
| rewrite vals_ev_app_l by (rewrite HL; lia); exact P5
| exact HR' | exact HK' | exact HBR
| eapply (heap_sw_post _ _ _ _ M'); [exact HH | exact HP | rewrite u_small by lia; lia | rewrite u_small by lia; lia] ] ]
end end end.
#[using="HIok uid Hva Hve Hvsp Htid Hplen DL Hsp Hal LEN ENVb model2"] Theorem hdr_short : ltac2:(TCodec.tc2 tcn__Ju0DrvC "@&@&7'S8y8%211vRL%5221u6%8221vRH&QM&QLvRM%3221%511p071").
Proof.
intros Hlt. unfold close_kg, Ju0DrvG.close_kg.
intros vals R M VM A1 HL P0 P48 P70 P1 P2 P3 P4 P5 HR HK HA HBR HC HH.
pose proof Hsp as Hsp'. pose proof Hal as Hal'.
specialize (HK 0%Z 5%Z ltac:(lia)). change (knG 0 5) with knGS in HK.
change (Env (vals_ev vals) (blobs_ev (blobs0 a0s path hw rdraw ++ [fdata]))) with (ENVb vals) in HR, HK |- *.
run_block_keep scr0 71%nat.
assert (HH1 : hi_heap HI [(A1, CAP)] crC M0 VM).
{ rewrite EQM. eapply (heap_block scfg L HI HIok sp0 Hsp' DL vals _ []); [exact P0 | intros i nb Hf; discriminate | vm_compute; reflexivity | exact HH]. }
clear EQM HH HA HC.
stdio_then_tail vals A1 71%nat scS msg_short msg_short_img 0x13245%Z err_tail_short HL P0 P48 P3 P4 P5 HR HK HH1 HBR.
Qed.
#[using="Hvsp Hplen HCAP HLEN Hsp LEN"] Lemma know_GL : ltac2:(TCodec.tc2 tcn__Ju0DrvC "RA'8'S8yR0%211%411';y8%611%311p061'B'>'9&7r3%22<1uR9%63521&R8r4uQ@%3221&S7r2%22F1%>3F41&QEvS6v2%332?1%N1G%J11&QI&R9r5%=2Q1@vRL%H2N1%645431(4%12:4%N3:31'?u6%2217r8uR7%M221&Q8%K2Q?1%Q73Q?31r9uR8%Q3221&Q9%Q12QE1%Q=3QE31&R6vCr:%211&QD+6+QooooO%3221%84Q05>1r;%911&Q?%<4Q42:1p051p0?1p0F1p0M1p0Q11p0Q>1p0QC1p0QL1p4R41pR8R61pVLR<1").
Proof.
intros vals M A1 HL P48 HZ HC H6 P71 P72 HK. pose proof B0_range as R0. pose proof B1_range as R1.
unfold knGL, kn_hdr. apply Forall_app. split; [|exact HK].
constructor; [|constructor; [|constructor; [|constructor; [|constructor]]]].
- eapply kbyte48; [exact P48 | exact HZ | exact HC | lia | cbn; lia | exact P71].
- eapply kbyte48; [exact P48 | exact HZ | exact HC | lia | cbn; lia | exact P72].
- eapply krange_lit; [exact P71 | lia | lia].
- eapply krange_lit; [exact P72 | lia | lia].
Qed.
#[using="HIok uid Hva Hve Hvsp Htid Hplen DL HCAP HLEN Hsp Hal ENVb model2"] Theorem hdr_overrun : ltac2:(TCodec.tc2 tcn__Ju0DrvC "H'?u6&7'S8y8%211vRL%5221%8271&R=vG&R;+6&Q;%3221%6251vRH&QM&QKvRM%3221%511p071p0?1").
Proof.
intros Hge Hov. unfold close_kg, Ju0DrvG.close_kg.
intros vals R M VM A1 HL P0 P48 P70 P1 P2 P3 P4 P5 HR HK HA HBR HC HH.
pose proof Hsp as Hsp'. pose proof Hal as Hal'.
pose proof (hz_of_block_range L sp0 DL _ _ HBR) as HZ. pose proof HZ as (Z1 & Z2 & Z3).
specialize (HK 6%Z 67108863%Z ltac:(lia)).
change (Env (vals_ev vals) (blobs_ev (blobs0 a0s path hw rdraw ++ [fdata]))) with (ENVb vals) in HR, HK |- *.
set (vals1 := vals ++ [Z_to_bv 64 B0; Z_to_bv 64 B1]).
assert (HL1 : length vals1 = 73%nat) by (subst vals1; rewrite length_app, HL; reflexivity).
assert (Y0 : vals_ev vals1 0 = sp0) by (subst vals1; rewrite vals_ev_app_l by (rewrite HL; lia); exact P0).
assert (Y3 : vals_ev vals1 3 = auxvp sp0 a0s path envv) by (subst vals1; rewrite vals_ev_app_l by (rewrite HL; lia); exact P3).
assert (Y4 : vals_ev vals1 4 = rnd sp0 a0s path envv) by (subst vals1; rewrite vals_ev_app_l by (rewrite HL; lia); exact P4).
assert (Y5 : vals_ev vals1 5 = tid) by (subst vals1; rewrite vals_ev_app_l by (rewrite HL; lia); exact P5).
assert (Y48 : vals_ev vals1 48 = Z_to_bv 64 A1) by (subst vals1; rewrite vals_ev_app_l by (rewrite HL; lia); exact P48).
assert (Y70 : vals_ev vals1 70 = Z_to_bv 64 LEN) by (subst vals1; rewrite vals_ev_app_l by (rewrite HL; lia); exact P70).
assert (Y71 : vals_ev vals1 71 = Z_to_bv 64 B0).
{ subst vals1. rewrite <- HL, <- (Nat.add_0_r (length vals)). rewrite vals_ev_app_r. reflexivity. }
assert (Y72 : vals_ev vals1 72 = Z_to_bv 64 B1).
{ subst vals1. replace 72%nat with (length vals + 1)%nat by (rewrite HL; reflexivity). rewrite vals_ev_app_r. reflexivity. }
pose proof (env_app_regs vals [Z_to_bv 64 B0; Z_to_bv 64 B1] _ srGL R ltac:(rewrite HL; vm_compute; reflexivity) HR) as HR1.
pose proof (env_app_know RSEGS vals [Z_to_bv 64 B0; Z_to_bv 64 B1] _ M (knG 6 67108863) ltac:(rewrite HL; vm_compute; reflexivity) HK) as HK0.
fold vals1 in HR1, HK0. change (Env (vals_ev vals1) (blobs_ev (blobs0 a0s path hw rdraw ++ [fdata]))) with (ENVb vals1) in HR1, HK0.
pose proof (know_GL vals1 M A1 HL1 Y48 HZ HC Hge Y71 Y72 HK0) as HK1.
clear HR HK HK0. rename HR1 into HR. rename HK1 into HK.
pose proof (hiv_facts' vals1 Y3 Y4) as HIV1.
clearbody vals1. clear HL P0 P1 P2 P3 P4 P5 P48 P70 vals.
run_blockH_keep scr_taken 73%nat.
{ apply (ltu_hdr_sc vals1 M true Y70 Y71 Y72). apply Z.ltb_lt. lia. }
assert (HH1 : hi_heap HI [(A1, CAP)] crC M0 VM).
{ rewrite EQM. eapply (heap_block scfg L HI HIok sp0 Hsp' DL vals1 _ []); [exact Y0 | intros i nb Hf; discriminate | vm_compute; reflexivity | exact HH]. }
clear EQM HH HA HC.
stdio_then_tail vals1 A1 73%nat scO msg_overrun msg_overrun_img 0x110b5%Z err_tail_overrun HL1 Y0 Y48 Y3 Y4 Y5 HR HK HH1 HBR.
Qed.
#[using="uid Hva Hve Hvsp Hplen DL HCAP HLEN Hsp Hal"] Theorem hdr_ok : ltac2:(TCodec.tc2 tcn__Ju0DrvC "G&R<&R;+6&Q;%3221vG%6221&QJ&Q=r1%211r2(:'M%211%411vRHr3%211p041p0:1pQ<>1p0@1").
Proof.
intros Hok KT HKT HKT0. unfold close_kg, Ju0DrvG.close_kg.
intros vals R M VM A1 HL P0 P48 P70 P1 P2 P3 P4 P5 HR HK HA HBR HC HH.
pose proof Hsp as Hsp'. pose proof Hal as Hal'.
pose proof (hz_of_block_range L sp0 DL _ _ HBR) as HZ. pose proof HZ as (Z1 & Z2 & Z3).
pose proof B0_range as HB0r. pose proof B1_range as HB1r. pose proof B2_range as HB2r. pose proof CFG_range as HCr.
assert (ELEN : LEN = Z.of_nat (length fdata)) by reflexivity.
assert (Hge : (6 <= length fdata)%nat) by lia.
specialize (HK 6%Z 67108863%Z ltac:(lia)).
change (Env (vals_ev vals) (blobs_ev (blobs0 a0s path hw rdraw ++ [fdata]))) with (ENVb vals) in HR, HK |- *.
set (vals1 := vals ++ [Z_to_bv 64 B0; Z_to_bv 64 B1]).
assert (HL1 : length vals1 = 73%nat) by (subst vals1; rewrite length_app, HL; reflexivity).
assert (Y0 : vals_ev vals1 0 = sp0) by (subst vals1; rewrite vals_ev_app_l by (rewrite HL; lia); exact P0).
assert (Y1 : vals_ev vals1 1 = p0 sp0 a0s path envv) by (subst vals1; rewrite vals_ev_app_l by (rewrite HL; lia); exact P1).
assert (Y2 : vals_ev vals1 2 = p1 sp0 a0s path envv) by (subst vals1; rewrite vals_ev_app_l by (rewrite HL; lia); exact P2).
assert (Y3 : vals_ev vals1 3 = auxvp sp0 a0s path envv) by (subst vals1; rewrite vals_ev_app_l by (rewrite HL; lia); exact P3).
assert (Y4 : vals_ev vals1 4 = rnd sp0 a0s path envv) by (subst vals1; rewrite vals_ev_app_l by (rewrite HL; lia); exact P4).
assert (Y5 : vals_ev vals1 5 = tid) by (subst vals1; rewrite vals_ev_app_l by (rewrite HL; lia); exact P5).
assert (Y48 : vals_ev vals1 48 = Z_to_bv 64 A1) by (subst vals1; rewrite vals_ev_app_l by (rewrite HL; lia); exact P48).
assert (Y70 : vals_ev vals1 70 = Z_to_bv 64 LEN) by (subst vals1; rewrite vals_ev_app_l by (rewrite HL; lia); exact P70).
assert (Y71 : vals_ev vals1 71 = Z_to_bv 64 B0).
{ subst vals1. rewrite <- HL, <- (Nat.add_0_r (length vals)). rewrite vals_ev_app_r. reflexivity. }
assert (Y72 : vals_ev vals1 72 = Z_to_bv 64 B1).
{ subst vals1. replace 72%nat with (length vals + 1)%nat by (rewrite HL; reflexivity). rewrite vals_ev_app_r. reflexivity. }
pose proof (env_app_regs vals [Z_to_bv 64 B0; Z_to_bv 64 B1] _ srGL R ltac:(rewrite HL; vm_compute; reflexivity) HR) as HR1.
pose proof (env_app_know RSEGS vals [Z_to_bv 64 B0; Z_to_bv 64 B1] _ M (knG 6 67108863) ltac:(rewrite HL; vm_compute; reflexivity) HK) as HK0.
fold vals1 in HR1, HK0. change (Env (vals_ev vals1) (blobs_ev (blobs0 a0s path hw rdraw ++ [fdata]))) with (ENVb vals1) in HR1, HK0.
pose proof (know_GL vals1 M A1 HL1 Y48 HZ HC Hge Y71 Y72 HK0) as HK1.
clear HR HK HK0. rename HR1 into HR. rename HK1 into HK.
clearbody vals1. clear HL P0 P1 P2 P3 P4 P5 P48 P70 vals.
run_blockH_keep scr_fall 73%nat.
{ apply (ltu_hdr_sc vals1 M false Y70 Y71 Y72). apply Z.ltb_ge. lia. }
cbn [mem_denot] in EQM. subst M0.
set (ext := [Z_to_bv 64 CFG; sx8F (Z_to_bv 64 B1);
Z_to_bv 64 (bv_unsigned (nth (Z.to_nat (2 + CFG)) fdata (Z_to_bv 8 0)));
Z_to_bv 64 (bv_unsigned (nth (Z.to_nat (3 + CFG)) fdata (Z_to_bv 8 0)));
Z_to_bv 64 (bv_unsigned (nth (Z.to_nat (4 + CFG)) fdata (Z_to_bv 8 0)));
Z_to_bv 64 (bv_unsigned (nth (Z.to_nat (5 + CFG)) fdata (Z_to_bv 8 0)))]).
set (vals2 := vals1 ++ ext).
assert (HL2 : length vals2 = 79%nat) by (subst vals2 ext; rewrite length_app, HL1; reflexivity).
assert (W0 : vals_ev vals2 0 = sp0) by (subst vals2; rewrite vals_ev_app_l by (rewrite HL1; lia); exact Y0).
assert (W1 : vals_ev vals2 1 = p0 sp0 a0s path envv) by (subst vals2; rewrite vals_ev_app_l by (rewrite HL1; lia); exact Y1).
assert (W2 : vals_ev vals2 2 = p1 sp0 a0s path envv) by (subst vals2; rewrite vals_ev_app_l by (rewrite HL1; lia); exact Y2).
assert (W3 : vals_ev vals2 3 = auxvp sp0 a0s path envv) by (subst vals2; rewrite vals_ev_app_l by (rewrite HL1; lia); exact Y3).
assert (W4 : vals_ev vals2 4 = rnd sp0 a0s path envv) by (subst vals2; rewrite vals_ev_app_l by (rewrite HL1; lia); exact Y4).
assert (W5 : vals_ev vals2 5 = tid) by (subst vals2; rewrite vals_ev_app_l by (rewrite HL1; lia); exact Y5).
assert (W48 : vals_ev vals2 48 = Z_to_bv 64 A1) by (subst vals2; rewrite vals_ev_app_l by (rewrite HL1; lia); exact Y48).
assert (W70 : vals_ev vals2 70 = Z_to_bv 64 LEN) by (subst vals2; rewrite vals_ev_app_l by (rewrite HL1; lia); exact Y70).
assert (W71 : vals_ev vals2 71 = Z_to_bv 64 B0) by (subst vals2; rewrite vals_ev_app_l by (rewrite HL1; lia); exact Y71).
assert (W72 : vals_ev vals2 72 = Z_to_bv 64 B1) by (subst vals2; rewrite vals_ev_app_l by (rewrite HL1; lia); exact Y72).
assert (WX : forall i, (i < 6)%nat -> vals_ev vals2 (73 + i) = nth i ext (Z_to_bv 64 0)).
{ intros i Hi. subst vals2. replace (73 + i)%nat with (length vals1 + i)%nat by (rewrite HL1; reflexivity).
rewrite vals_ev_app_r. reflexivity. }
pose proof (WX 0%nat ltac:(lia)) as W73. pose proof (WX 1%nat ltac:(lia)) as W74.
pose proof (WX 2%nat ltac:(lia)) as W75. pose proof (WX 3%nat ltac:(lia)) as W76.
pose proof (WX 4%nat ltac:(lia)) as W77. pose proof (WX 5%nat ltac:(lia)) as W78.
cbn [nth ext Nat.add] in W73, W74, W75, W76, W77, W78. clear WX.
pose proof (env_app_regs vals1 ext _ srHa _ ltac:(rewrite HL1; vm_compute; reflexivity) HR) as HR1.
pose proof (env_app_know RSEGS vals1 ext _ M knGL ltac:(rewrite HL1; vm_compute; reflexivity) HK) as HK0.
fold vals2 in HR1, HK0. change (Env (vals_ev vals2) (blobs_ev (blobs0 a0s path hw rdraw ++ [fdata]))) with (ENVb vals2) in HR1, HK0.
assert (Ecfg : edenot (ENVb vals2) cfglen_x = edenot (ENVb vals2) (EVar 73)).
{ unfold ENVb, ENV. rewrite cfglen_x_cfgF, W71, W72, cfgF_val by lia. fold CFG. symmetry. exact W73. }
assert (Esx8 : edenot (ENVb vals2) sx8_x = edenot (ENVb vals2) (EVar 74)).
{ unfold ENVb, ENV. rewrite sx8_x_sx8F, W72. symmetry. exact W74. }
pose proof (regs_ok_esub _ _ _ _ _ Esx8 (regs_ok_esub _ _ _ _ _ Ecfg HR1)) as HR2.
lazymatch type of HR2 with regs_ok ?Ex ?srx ?Rx => assert (HRb : regs_ok Ex srHb0 Rx) by (exact HR2) end.
clear HR HR1 HR2. rename HRb into HR.
assert (HKb : know_ok RSEGS (ENVb vals2) M knHb0).
{ unfold knHb0, kn_bm. apply Forall_app. split; [|exact HK0].
assert (PXv : edenot (ENVb vals2) PX = Z_to_bv 64 (A1 + CFG)).
{ cbn [edenot ev ENVb ENV PX]. rewrite W48, W73. apply alu_add_Z. }
assert (KB : forall (j : Z) (v : nat), (2 <= j <= 5)%Z ->
vals_ev vals2 v = Z_to_bv 64 (bv_unsigned (nth (Z.to_nat (j + CFG)) fdata (Z_to_bv 8 0))) ->
kentry_ok RSEGS (ENVb vals2) M (KWord (SA PX j) 1 (EVar v))).
{ intros j v Hj Pv. cbn [kentry_ok]. split; [lia|]. split.
- unfold flat, estart. cbn [a_base a_off]. rewrite PXv, u_small by lia. lia.
- unfold adenot, v_addi. cbn [a_base a_off]. rewrite PXv, u_small by lia.
change (edenot (ENVb vals2) (EVar v)) with (vals_ev vals2 v). rewrite Pv.
replace (A1 + CFG + j)%Z with (A1 + Z.of_nat (Z.to_nat (j + CFG)))%Z by lia.
apply content_byte; [exact HC | lia | lia | lia]. }
constructor; [eapply krange_lit; [exact W73 | lia | lia]|].
constructor; [apply (KB 2%Z); [lia | exact W75]|].
constructor; [apply (KB 3%Z); [lia | exact W76]|].
constructor; [apply (KB 4%Z); [lia | exact W77]|].
constructor; [apply (KB 5%Z); [lia | exact W78]|].
assert (BR : forall (v : nat) k, vals_ev vals2 v = Z_to_bv 64 (bv_unsigned (nth k fdata (Z_to_bv 8 0))) ->
kentry_ok RSEGS (ENVb vals2) M (KRange (EVar v) 0 255)).
{ intros v k Pv. pose proof (bv_unsigned_in_range _ (nth k fdata (Z_to_bv 8 0))) as Hb. change (bv_modulus 8) with 256%Z in Hb.
eapply krange_lit; [exact Pv | lia | lia]. }
constructor; [exact (BR _ _ W75)|]. constructor; [exact (BR _ _ W76)|].
constructor; [exact (BR _ _ W77)|]. constructor; [exact (BR _ _ W78)|]. constructor. }
clear HK HK0. rename HKb into HK.
pose proof (hiv_facts' vals2 W3 W4) as HIV2.
clearbody vals2. clear ext HL1 Y0 Y1 Y2 Y3 Y4 Y5 Y48 Y70 Y71 Y72 vals1.
run_blockH_keep scr0 79%nat.
cbn [mem_denot] in EQM. subst M0.
set (ext2 := [Z_to_bv 64 PL; Z_to_bv 64 B2]).
set (vals3 := vals2 ++ ext2).
assert (HL3 : length vals3 = 81%nat) by (subst vals3 ext2; rewrite length_app, HL2; reflexivity).
assert (V79 : vals_ev vals3 79 = Z_to_bv 64 PL).
{ subst vals3. rewrite <- HL2, <- (Nat.add_0_r (length vals2)). rewrite vals_ev_app_r. reflexivity. }
assert (V80 : vals_ev vals3 80 = Z_to_bv 64 B2).
{ subst vals3. replace 80%nat with (length vals2 + 1)%nat by (rewrite HL2; reflexivity). rewrite vals_ev_app_r. reflexivity. }
pose proof (env_app_regs vals2 ext2 _ srHb _ ltac:(rewrite HL2; vm_compute; reflexivity) HR) as HR1.
pose proof (env_app_know RSEGS vals2 ext2 _ M knHb0 ltac:(rewrite HL2; vm_compute; reflexivity) HK) as HK0.
fold vals3 in HR1, HK0. change (Env (vals_ev vals3) (blobs_ev (blobs0 a0s path hw rdraw ++ [fdata]))) with (ENVb vals3) in HR1, HK0.
assert (T70 : vals_ev vals3 70 = Z_to_bv 64 LEN) by (subst vals3; rewrite vals_ev_app_l by (rewrite HL2; lia); exact W70).
assert (T73 : vals_ev vals3 73 = Z_to_bv 64 CFG) by (subst vals3; rewrite vals_ev_app_l by (rewrite HL2; lia); exact W73).
assert (T48 : vals_ev vals3 48 = Z_to_bv 64 A1) by (subst vals3; rewrite vals_ev_app_l by (rewrite HL2; lia); exact W48).
assert (Epl : edenot (ENVb vals3) plen_x = edenot (ENVb vals3) (EVar 79)).
{ unfold ENVb, ENV. rewrite (plen_val LEN CFG vals3 _ ltac:(lia) ltac:(lia) T70 T73). symmetry. exact V79. }
pose proof (regs_ok_esub _ _ _ _ _ Epl HR1) as HR2.
lazymatch type of HR2 with regs_ok ?Ex ?srx ?Rx => assert (HRt : regs_ok Ex srT0 Rx) by (exact HR2) end.
clear HR HR1 HR2.
assert (HKt : know_ok RSEGS (ENVb vals3) M knT0).
{ eapply ksubl_sound; [|exact knT0_sub]. apply Forall_app. split; [|exact HK0]. unfold kn_tgt.
constructor; [eapply krange_lit; [exact T73 | lia | lia]|].
constructor; [eapply krange_lit; [exact V79 | unfold PL; lia | unfold PL; lia]|].
constructor; [eapply kbyte48; [exact T48 | exact HZ | exact HC | lia | cbn; lia | exact V80]|].
constructor; [eapply krange_lit; [exact V80 | lia | lia]|]. constructor. }
clear HK HK0.
lazymatch type of HRt with regs_ok _ _ ?Rx =>
apply (HKT vals3 Rx M VM A1 HL3); try assumption;
try (subst vals3; rewrite vals_ev_app_l by (rewrite HL2; lia); assumption) end.
Qed.
End DrvC.
End FPX_1.
