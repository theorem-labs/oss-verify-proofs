(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require BvWfKernel.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.LinuxProcessSem.Checks.Sys Require Import Mm.Mmap.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import SimInv ExitSim CatSim MmapSim AllocSim AllocSim2 WallSim.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Export Scfg.
Import ListNotations.
Open Scope bv_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require TCodec.
Ltac2 tcn__ShapeAlg () := ([""; "Corelib.Init.Datatypes."; "Corelib.Init.Logic."; "Corelib.Init.Peano."; "Corelib.Init.Specif."; "Corelib.Lists.ListDef."; "Corelib.Numbers.BinNums."; "LinuxProcessSemantics.LinuxProcessSem.BvBase."; "LinuxProcessSemantics.LinuxProcessSem.Fs."; "LinuxProcessSemantics.LinuxProcessSem.MemImageType."; "LinuxProcessSemantics.LinuxProcessSem.Monad."; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics."; "LinuxProcessSemantics.LinuxProcessSem.Run."; "LinuxProcessSemantics.LinuxProcessSem.Specs."; "LinuxProcessSemantics.LinuxProcessSem.State."; "LinuxProcessSemantics.LinuxProcessSem.Sys.Syscall."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.AllocSim2."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CatSim."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.ExitSim."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.MmapSim."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.ShapeAlg."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.ShapeAlg.Bridges."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.ShapeAlg.WithSegs."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.WallSim."; "Stdlib.Lists.List."; "stdpp.bitvector.definitions."], [["0A"; "0B"; "1None"; "1O"; "1Some"; "1app"; "1bool"; "1cons"; "1false"; "1length"; "1list"; "1nat"; "1nil"; "1option"; "1pair"; "1prod"]; ["1true"; "1tt"; "1unit"; "2and"; "2eq"; "2ex"; "2iff"; "2not"; "2or"; "3le"; "4proj1_sig"; "4sig"; "5Forall"; "5firstn"; "5map"; "5skipn"]; ["6Z"; "7len_word"; "8Fs"; "9Segment"; ":Ok"; ":Unmodeled"; ";MachineOk"; ";machine_result"; ";machine_state"; ";ms_gpr"; ";ms_read_bytes"; ";ms_svc_pending"; ";set_gpr0"; ";step"; "<SError"; "<SNext"]; ["<advance_past_svc"; "<apply_effect"; "<cfg_model"; "<config"; "<is_prefix"; "<mkCfg"; "<obs_trace_cfg"; "<reaches_error_cfg"; "<refusal_b"; "<sc_alloc"; "<spurious_refusal_cfg"; "<sstep_cfg"; "<star_cfg"; "<step_to"; "<sys_input"; "=syscall_spec"]; [">ENOMEM"; ">ExitEv"; ">MemCopy"; ">Model"; ">SyscallEffect"; ">WriteEv"; ">errno_ret"; ">event"; ">m_fs"; ">m_halted"; ">m_vm_lazy"; ">materialize_model_accesses"; ">mkEffectU"; ">page_round_up_Z"; ">syscall_effect_accesses"; ">with_halted"]; ["?fd32"; "@two_outcomes"; "Abuf_modeled"; "Abufs_modeled"; "Afd1chan"; "Afdchan"; "Amsteps"; "Ato_wexit"; "Ato_wexit_ch"; "Awevents"; "Awevents_ch"; "Awpick"; "Bis_exit_no"; "Cgrant_ok"; "Cmmap_args_ok"; "Cmmap_model"]; ["Cmunmap_args_ok"; "Cmunmap_eff"; "Cmunmap_model"; "Cpage_round_up"; "Ctwm"; "Ctwm_pend"; "Ctwm_tail"; "Ctwo_traces"; "Et_outcomes"; "Et_writes_ch_pick"; "DTSet"; "Fmmap_grant_eff"; "Fnode_ok"; "Fpnode_ok"; "Frealizes"; "Frz_path"]; ["Dhalt_ev"; "Dnode_ok"; "Drealizes"; "Dt_alt"; "Dt_alt2"; "Dt_emit"; "Dt_eq"; "Dt_exit"; "Dt_write_ch"; "Dt_writes"; "Dt_writes_ch"; "Dt_writes_pick"; "Dwr_index"; "Gto_wall"; "Gto_wall_tail"; "Gto_wallexit"]; ["Hfold_right"; "0T"; "0T'"; "0T1"; "0T2"; "0T3"; "0a"; "0b"; "0bf"; "0bs"; "0buf"; "0bufs"; "0c"; "0c'"; "0cf"; "0ch"]; ["0code"; "0cs"; "0e"; "0eff"; "0evs"; "0f"; "0fd"; "0fs"; "0full"; "0i"; "0k"; "0model"; "0model'"; "0model''"; "0ms"; "0ms'"]; ["0n"; "0rest"; "0scfg"; "0segs"; "0st"; "IZ_to_bv"; "Ibv"; "Ibv_and"; "Ibv_unsigned"; "0tr"; "0tr'"; "0x"; "0x8"]]).
Lemma is_prefix_app_r {A} : forall (l m a : list A),
is_prefix a l -> is_prefix a (l ++ m).
Proof.
induction l as [|x l IH]; intros m a H.
- destruct a; [apply is_prefix_nil | cbn in H; contradiction].
- destruct a as [|y a]; cbn in *; [exact I|].
destruct H as [-> H]. split; [reflexivity | apply IH; exact H].
Qed.
Lemma is_prefix_app_split {A} : forall (l a b : list A),
is_prefix b (l ++ a) ->
is_prefix b l \/ exists b', b = l ++ b' /\ is_prefix b' a.
Proof.
induction l as [|x l IH]; intros a b H.
- right. exists b. split; [reflexivity | exact H].
- destruct b as [|y b]; cbn in H; [left; exact I|].
destruct H as [-> H]. destruct (IH a b H) as [Hp | (b' & -> & Hp)].
+ left. cbn. split; [reflexivity | exact Hp].
+ right. exists b'. split; [reflexivity | exact Hp].
Qed.
Lemma is_prefix_nil_r {A} : forall (a : list A), is_prefix a [] -> a = [].
Proof. destruct a; cbn; [reflexivity | contradiction]. Qed.
Definition TSet := list event -> Prop.
Definition t_eq (T T' : TSet) : Prop := forall tr, T tr <-> T' tr.
Lemma t_eq_refl : ltac2:(TCodec.tc2 tcn__ShapeAlg "5&S:&SFr1%2211pX441"). Proof. firstorder. Qed.
Lemma t_eq_sym : ltac2:(TCodec.tc2 tcn__ShapeAlg ":&S:&SFr2r1%3221r3%5241p031pX681pX491"). Proof. firstorder. Qed.
Lemma t_eq_trans : ltac2:(TCodec.tc2 tcn__ShapeAlg "<&S:&SFr3r2%3221r5%5214p031p041pX<91pX::1pX8;1").
Proof. firstorder. Qed.
Definition t_nil : TSet := fun tr => tr = [].
Definition t_emit (evs : list event) (T : TSet) : TSet :=
fun tr => is_prefix tr evs \/ exists tr', tr = evs ++ tr' /\ T tr'.
Definition t_alt {I : Type} (f : I -> TSet) : TSet := fun tr => exists i, f i tr.
Definition t_alt2 (A B : TSet) : TSet := fun tr => A tr \/ B tr.
Definition t_exit (code : word) (fs : Fs.Fs) : TSet :=
t_emit [ExitEv code fs] t_nil.
Definition wr_index (buf : list byte) : Type :=
{n : nat | (1 <= n)%nat /\ (n <= length buf)%nat}.
Definition wr_full (buf : list byte) (Hnb : (1 <= length buf)%nat)
: wr_index buf :=
exist _ (length buf) (conj Hnb (Nat.le_refl _)).
Definition t_write_ch (ch : word) (buf : list byte) (T : TSet) : TSet :=
t_alt (fun i : wr_index buf =>
t_emit (map (WriteEv ch) (firstn (proj1_sig i) buf)) T).
Definition t_writes_pick (bufs : list (list byte)) (T : TSet) : TSet :=
fold_right (t_write_ch (Z_to_bv 64 1)) T bufs.
Lemma t_emit_nil_eq : ltac2:(TCodec.tc2 tcn__ShapeAlg "@':'R7%211!pZH21r1(<%116%311&SF&SEr2%2251%4212p061pX4;1").
Proof.
intros T H0 tr. unfold t_emit. split.
- intros [Hp | (tr' & -> & HT)];
[apply is_prefix_nil_r in Hp; subst tr; exact H0 | exact HT].
- intro HT. right. exists tr. split; [reflexivity | exact HT].
Qed.
Lemma t_writes_pick_nil : ltac2:(TCodec.tc2 tcn__ShapeAlg ">&S:'D&SK(<':'U6y8%211%411%611r1%9221%;3<12pX4=1"). Proof. reflexivity. Qed.
Lemma t_writes_pick_cons : ltac2:(TCodec.tc2 tcn__ShapeAlg "J':'U6y8%211%411%511&S:'D&SK(7r3r2%33821r1%6221&SH&U5yR0+1%3221%<297%632;1%?3@81pX4A1pXHC1pXFE1").
Proof. reflexivity. Qed.
Definition t_writes_ch (ch : word) (bufs : list (list byte)) (T : TSet) : TSet :=
fold_right (fun buf acc => t_emit (map (WriteEv ch) buf) acc) T bufs.
Definition t_writes (bufs : list (list byte)) (T : TSet) : TSet :=
t_writes_ch (Z_to_bv 64 1) bufs T.
Lemma t_writes_nil : ltac2:(TCodec.tc2 tcn__ShapeAlg ">&S:'D&SI(<':'U6y8%211%411%611r1%9221%;3<12pX4=1"). Proof. reflexivity. Qed.
Lemma t_writes_cons : ltac2:(TCodec.tc2 tcn__ShapeAlg "O':'U6y8%211%411%511&S:'D&SI(7r3r2%33821r1%6221&SE&N'R7(R5&U5yR0+1%3221%511%84E71>%A2><%;221%D3E=1pX4F1pXHH1pXFJ1").
Proof. reflexivity. Qed.
Lemma t_writes_ch_cons : ltac2:(TCodec.tc2 tcn__ShapeAlg "O'U6yR0%211':y8%511%311%411&S:'D&SJr4(7r3r2%33921r1%73621&SE&N'R7(R5%11;%44B31:%>3=:8%7221%A3B91pX4C1pXHE1pXFG1pY0L1").
Proof. reflexivity. Qed.
Lemma t_emit_has_nil : ltac2:(TCodec.tc2 tcn__ShapeAlg "<':'R7%211&S:&SEr2r1(<%117%53431pX471pY691").
Proof. intros e T. left. apply is_prefix_nil. Qed.
Lemma t_writes_ch_exit_has_nil : ltac2:(TCodec.tc2 tcn__ShapeAlg "H'U6yR0%211':y8%511%311%411&Q2&SJr4r3&SGr2r1%3221(<'R7%211%:49841pY@<1pY2C1pXH?1pY0E1").
Proof.
intros ch [|b bs] code fs; cbn [t_writes_ch fold_right];
apply t_emit_has_nil.
Qed.
Lemma t_writes_ch_exit_iff : ltac2:(TCodec.tc2 tcn__ShapeAlg "Q7'U6yR0%211':y8%511%311%411&Q2'R7%711&F&SJr5r4&SGr3r2%3221r1%847621&QD&5&RJ%12;:(7(R1%12;:(<%11D%53E31%93F71%;3G=1%F2=1pZDH1pY@K1pY2Q21pXHN1pY0Q41").
Proof.
intros ch bufs; induction bufs as [|buf bufs IH]; intros code fs tr.
- cbn [wevents_ch app]. unfold t_writes_ch, fold_right, t_exit, t_emit, t_nil.
split.
+ intros [H | (tr' & -> & ->)]; [exact H | rewrite app_nil_r; apply is_prefix_refl].
+ intro H. left. exact H.
- rewrite t_writes_ch_cons. cbn [wevents_ch]. rewrite <- app_assoc.
unfold t_emit at 1. split.
+ intros [H | (tr' & -> & Hc)].
* apply is_prefix_app_r; exact H.
* apply is_prefix_app_mono. apply IH. exact Hc.
+ intro H. apply is_prefix_app_split in H as [H | (tr' & -> & H)].
* left; exact H.
* right. exists tr'. split; [reflexivity | apply IH; exact H].
Qed.
Lemma t_writes_exit_iff : ltac2:(TCodec.tc2 tcn__ShapeAlg "Q5':'U6y8%211%411%511yR0%611&Q2'R7%:11&F&SIr4&SGr3r2%3221r1%73621&QD&5&RI%11:(7(R1%12;:(<%11C%53D31%93E71%;3F=1%E2=1pZDG1pY@J1pY2L1pXHO1").
Proof.
intros bufs code fs tr. unfold t_writes.
rewrite t_writes_ch_exit_iff, wevents_ch_fd1. reflexivity.
Qed.
Lemma t_alt_wall : ltac2:(TCodec.tc2 tcn__ShapeAlg "QJ'U6yR0%211':y8%511%311&S:r1(<'R7%211%411'Iu1&9r3%22<1%5241&SF&SC&SLr4%211&SE&N(R5r6%211&M&J';'C%D2CI%C2M7%F2K1%4231qZ261%8371Nr5%;3Q321%@4Q4O=1&O%13Q654%C4Q7Q2@1%E21G%F251qYDH1%L2I1%G1:%I4Q=Q81L%K21Q3%Q1241p0Q31p0Q:1pX4Q@1pZ4QB1pY0QG1").
Proof.
intros ch rest T HT Hnb tr. split.
- intros [[n [Hn1 Hn2]] Hi]. cbn [proj1_sig] in Hi.
destruct Hi as [Hp | (tr1 & -> & Hi)].
+ left. eapply is_prefix_trans; [exact Hp|].
rewrite <- (firstn_skipn n rest) at 2. rewrite map_app.
apply is_prefix_app_r. apply is_prefix_refl.
+ destruct Hi as [Hp | (tr2 & -> & Ht)].
* left.
rewrite <- (firstn_skipn n rest) at 2. rewrite map_app.
apply is_prefix_app_mono. exact Hp.
* right. exists tr2. split; [|exact Ht].
rewrite app_assoc, <- map_app, firstn_skipn. reflexivity.
- intros [Hp | (tr' & -> & Ht)].
+ exists (wr_full rest Hnb). unfold wr_full. cbn [proj1_sig].
rewrite firstn_all. left. exact Hp.
+ exists (wr_full rest Hnb). unfold wr_full. cbn [proj1_sig].
rewrite firstn_all, skipn_all. right.
exists tr'. split; [reflexivity|].
cbn [map]. right. exists tr'. split; [reflexivity | exact Ht].
Qed.
Lemma t_writes_ch_pick_exit_iff : ltac2:(TCodec.tc2 tcn__ShapeAlg "QJ'U6yR0%211':y8%511%311%411&Q2'R7%711'L'Iu1&9r1%22;1%5241qX@<1r4%93>21&F&T0&S:&SHr6%211&SGr3%22:1r5r2%:69J6321'E'C'RKr7%231<F&QD&5(7(R1%12<G(<%11Q3%53Q431%73Q5O1%93Q6C1%>2;1qYBQ71%A2Q81%N2C1p0Q01pZDQ;1pY@Q>1pY2QE1pXHQA1pY0QG1").
Proof.
intros ch bufs code fs tr Hall; revert tr;
induction Hall as [|buf bufs Hnb Hall IH]; intros tr.
- cbn [fold_right]. unfold t_exit, t_emit, t_nil.
split.
+ intros [H | (tr' & -> & ->)].
* exists []. split; [apply wp_nil | exact H].
* exists []. split; [apply wp_nil|].
rewrite app_nil_r. cbn [app]. apply is_prefix_refl.
+ intros (full & Hw & Hp). inversion Hw; subst full.
left. exact Hp.
- cbn [fold_right]. unfold t_write_ch at 1, t_alt at 1.
split.
+ intros [[n [Hn1 Hn2]] Hi]. cbn [proj1_sig] in Hi.
destruct Hi as [H | (tr' & -> & Hc)].
* exists (map (WriteEv ch) (firstn n buf) ++ wevents_ch ch bufs).
split; [apply wp_cons; [exact Hn1 | exact Hn2 | apply wpick_wevents; exact Hall]|].
rewrite <- app_assoc.
eapply is_prefix_trans; [exact H | apply is_prefix_app_r; apply is_prefix_refl].
* apply IH in Hc. destruct Hc as (full & Hw & Hp).
exists (map (WriteEv ch) (firstn n buf) ++ full).
split; [apply wp_cons; assumption|].
rewrite <- app_assoc. apply is_prefix_app_mono. exact Hp.
+ intros (full & Hw & Hp).
inversion Hw as [|buf' bufs' n tr0 Hn1 Hn2 Hw0]; subst.
rewrite <- app_assoc in Hp.
apply is_prefix_app_split in Hp as [Hp | (tr' & -> & Hp)].
* exists (exist _ n (conj Hn1 Hn2)). cbn [proj1_sig]. left. exact Hp.
* exists (exist _ n (conj Hn1 Hn2)). cbn [proj1_sig]. right.
exists tr'. split; [reflexivity|].
apply IH. exists tr0. split; assumption.
Qed.
Lemma t_writes_pick_exit_iff : ltac2:(TCodec.tc2 tcn__ShapeAlg "QH':'U6y8%211%411%511yR0%611&Q2'R7%:11'L'Iu1&9r1%22=1%5241qX@>1r4%93@21&F&SKr5&SGr3%2271r2%63521'E'C'RK&U5+1%22L1r6%5321E&QD&5(7(R1%12BF(<%11Q2%53Q331%73Q4N1%93Q5E1%A2;1qYBQ61%D2Q71%M2F1p0O1pZDQ:1pY@Q=1pY2Q?1pXHQB1").
Proof. intros. apply t_writes_ch_pick_exit_iff. assumption. Qed.
Lemma two_traces_t_alt2 : ltac2:(TCodec.tc2 tcn__ShapeAlg "Q3':'U6y8%211%411%511yR0%611&Q2'R7%:11&F&SD&SIr6&SGr5r2%3221%6251r4r3%7215%:231r1%=3621&S7%16=;76:3%A231pZDC1pY@F1pY4H1pXDK1pXNJ1pXBM1").
Proof.
intros. unfold t_alt2, MmapSim.two_traces.
rewrite !t_writes_exit_iff. reflexivity.
Qed.
Definition halt_ev (m' : Model) (code : word) : event :=
match m_killed m' with
| Some sig => KillEv sig (m_fs m')
| None => ExitEv code (m_fs m')
end.
Section WithSegs.
Variable segs : list Segment.
Variable scfg : SpuriousCfg.
Definition node_ok (c : config) (I : Type)
(evs : I -> list event) (nx : I -> config) : Prop :=
(forall i, sstep_cfg segs scfg c (evs i) (SNext (nx i)))
/\ (forall e st, sstep_cfg segs scfg c e st -> exists i, e = evs i /\ st = SNext (nx i)).
Definition pnode_ok (c : config) (I : Type)
(evs : I -> list event) (nx : I -> config) : Prop :=
(forall i, sstep segs c (evs i) (SNext (nx i)))
/\ (forall e st, sstep segs c e st -> exists i, e = evs i /\ st = SNext (nx i)).
Lemma node_ok_of_pnode : forall c I evs nx,
pnode_ok c I evs nx ->
fam_on segs scfg (cfg_ms c) ->
node_ok c I evs nx.
Proof.
intros c I evs nx [Hcomp Hsound] Hon. split.
- intros i. apply sstep_cfg_of_sstep'; [apply Hcomp | exact Hon].
- intros e st Hss. apply Hsound. eapply sstep_cfg_sub. exact Hss.
Qed.
Lemma node_ok_of_pnode_instr : forall c I evs nx,
ms_svc_pending (cfg_ms c) = None ->
pnode_ok c I evs nx ->
node_ok c I evs nx.
Proof.
intros c I evs nx Hsvc Hp. apply node_ok_of_pnode; [exact Hp|].
apply fam_on_instr. exact Hsvc.
Qed.
Lemma node_ok_of_pnode_sysno : forall ms model x8 n I evs nx,
ms_svc_pending ms = Some x8 ->
bv_unsigned x8 = n ->
injected_arm n = None ->
pnode_ok (mkCfg ms model) I evs nx ->
node_ok (mkCfg ms model) I evs nx.
Proof.
intros ms model x8 n I evs nx Hsvc Hn Harm Hp.
apply node_ok_of_pnode; [exact Hp|]. eapply fam_on_sysno; eassumption.
Qed.
Lemma node_of_iff : forall c (I J : Type) (evs : I -> list event) (nx : I -> config)
(f : J -> I),
(forall i, exists j, f j = i) ->
node_ok c I evs nx ->
node_ok c J (fun j => evs (f j)) (fun j => nx (f j)).
Proof.
intros c I J evs nx f Hsurj [Hc Hs]. split.
- intros j. apply Hc.
- intros e st Hss. destruct (Hs e st Hss) as (i & -> & ->).
destruct (Hsurj i) as (j & <-). exists j. split; reflexivity.
Qed.
Inductive realizes : config -> TSet -> Prop :=
| rz_node : forall c (I : Type) (evs : I -> list event) (nx : I -> config)
(T : I -> TSet) (i0 : I),
node_ok c I evs nx ->
(forall i, realizes (nx i) (T i)) ->
realizes c (t_alt (fun i => t_emit (evs i) (T i)))
| rz_halt : forall c,
m_halted (cfg_model c) <> None ->
realizes c t_nil
| rz_conseq : forall c T T',
realizes c T -> t_eq T T' -> realizes c T'.
Lemma realizes_nonempty : ltac2:(TCodec.tc2 tcn__ShapeAlg "='QC&S:'S>r2r1%3221(<'R7%211%611p051pX4:1pXJ<1").
Proof.
intros c T H; induction H as [c I evs nx T i0 Hnode Hcont IH | c Hh | c T T' H IH Heq].
- exists i0. left. apply is_prefix_nil.
- reflexivity.
- apply Heq. exact IH.
Qed.
Lemma realizes_pclosed : ltac2:(TCodec.tc2 tcn__ShapeAlg "G'QC&S:'S>r2r1%3221':'R7%211r4%117&QDr3%236:1r6%113p031p071pZF:1pZD;1p0?1pX4D1pXJF1").
Proof.
intros c T H; induction H as [c I evs nx T i0 Hnode Hcont IH | c Hh | c T T' H IH Heq];
intros tr tr' HT Hp.
- destruct HT as [i [Hpre | (tr0 & -> & HT0)]]; exists i.
+ left. eapply is_prefix_trans; eauto.
+ apply is_prefix_app_split in Hp as [Hp | (tr0' & -> & Hp)].
* left. exact Hp.
* right. exists tr0'. split; [reflexivity | eapply IH; eauto].
- unfold t_nil in *. subst tr. apply is_prefix_nil_r in Hp. exact Hp.
- apply Heq. eapply IH; [apply Heq; exact HT | exact Hp].
Qed.
Lemma realizes_star_only : ltac2:(TCodec.tc2 tcn__ShapeAlg "F'QC&S:'S>r2r1%3221':'R7%211'QLvU3vU2r5%45321:9r3%311p031pXLA1pZD:1p0>1pX4C1pXJE1").
Proof.
intros c T H; induction H as [c I evs nx T i0 Hnode Hcont IH | c Hh | c T T' H IH Heq];
intros tr c' Hstar.
- inversion Hstar as [|c1 e c2 tr2 c3 Hss Hstar2]; subst.
+ exists i0. left. apply is_prefix_nil.
+ destruct Hnode as [_ Hsound].
destruct (Hsound e (SNext c2) Hss) as (i & -> & Heq2).
inversion Heq2; subst c2.
exists i. right. exists tr2. split; [reflexivity | eapply IH; exact Hstar2].
- destruct (star_cfg_halted_nil segs scfg c tr c' Hh Hstar) as [-> _]. reflexivity.
- apply Heq. eapply IH; exact Hstar.
Qed.
Lemma realizes_admits : ltac2:(TCodec.tc2 tcn__ShapeAlg "E'QC&S:'S>r2r1%3221':'R7%211r3%116&QFvU3vU2r5%44321<p061pZD91p0=1pX4B1pXJD1").
Proof.
intros c T H; induction H as [c I evs nx T i0 Hnode Hcont IH | c Hh | c T T' H IH Heq];
intros tr HT.
- destruct Hnode as [Hcomp _].
destruct HT as [i [Hpre | (tr0 & -> & HT0)]].
+ exists (evs i), (nx i). split; [apply star_cfg_one; apply Hcomp | exact Hpre].
+ destruct (IH i tr0 HT0) as (tr'' & c'' & Hstar & Hp).
exists (evs i ++ tr''), c''.
split; [eapply star_cfg_step; [apply Hcomp | exact Hstar] | apply is_prefix_app_mono; exact Hp].
- unfold t_nil in HT; subst tr. apply obs_trace_cfg_nil.
- apply IH. apply Heq. exact HT.
Qed.
Theorem realizes_obs_iff : ltac2:(TCodec.tc2 tcn__ShapeAlg "F'QC&S:'S>r2r1%3221':'R7%211&F&QFvU3vU2r4%44321:r3%11<%8231pZD:1p0>1pX4C1pXJE1").
Proof.
intros c T H tr. split.
- intros (tr' & c' & Hstar & Hp).
eapply realizes_pclosed; [exact H | eapply realizes_star_only; eauto | exact Hp].
- apply realizes_admits; exact H.
Qed.
Lemma sstep_halted_none : ltac2:(TCodec.tc2 tcn__ShapeAlg "N'QC':'R7%211'QM'QKvU3vU2r3r2r1%6554321'D'='U6yR0%211%411&R9&QBr4%211%411(2%118%=3831p0?1pZ:G1pY6I1pXJM1").
Proof. exact (sstep_cfg_halted_none segs scfg). Qed.
Lemma realizes_step : ltac2:(TCodec.tc2 tcn__ShapeAlg "L'QC&S:':'R7%211'S>r4r3%3221'QKvU3vU2r5(Q?r2%211%7565491'Er1%>2=1qX6C1%42D1p061p0?1pXLH1pY6E1pX4I1pXJK1").
Proof.
intros c T e c' H; revert e c';
induction H as [c I evs nx T i0 Hnode Hcont IH | c Hh | c T T' H IH Heq];
intros e c' Hss.
- destruct Hnode as [_ Hsound].
destruct (Hsound e (SNext c') Hss) as (i & _ & Heq2).
inversion Heq2; subst c'. exists (T i). apply Hcont.
- exfalso. apply Hh. eapply sstep_halted_none; exact Hss.
- eapply IH; exact Hss.
Qed.
Lemma realizes_no_sserror : ltac2:(TCodec.tc2 tcn__ShapeAlg "E'QC&S:':'R7%211'S>r3r2%3221&G'QKvU3vU2r4(Q>%5543281%711p091pY6>1pX4B1pXJD1").
Proof.
intros c T e H; revert e;
induction H as [c I evs nx T i0 Hnode Hcont IH | c Hh | c T T' H IH Heq];
intros e Hss.
- destruct Hnode as [_ Hsound].
destruct (Hsound e SError Hss) as (i & _ & Hbad). discriminate.
- apply Hh. eapply sstep_halted_none; exact Hss.
- eapply IH; exact Hss.
Qed.
Definition rz_path (c : config) : Prop := exists T, realizes c T.
Lemma rz_path_star : ltac2:(TCodec.tc2 tcn__ShapeAlg "B'QC':'R7%211&S?r3%211'QLvU3vU2r4r2%5543271p017p081pXL?1pZD=1pXJA1").
Proof.
intros c tr c' Hp Hstar. induction Hstar as [c | c1 evs c2 tr c3 Hss Hstar IH].
- exact Hp.
- apply IH. destruct Hp as [T HT].
destruct (realizes_step c1 T evs c2 HT Hss) as [T' HT']. exists T'. exact HT'.
Qed.
Theorem realizes_no_error : ltac2:(TCodec.tc2 tcn__ShapeAlg "@'QC&S:'S>r2r1%3221&G&QGvU3vU2r3%43321%611p081pX4=1pXJ?1").
Proof.
intros c T H (tr & c' & evs & Hstar & Herr).
assert (Hp : rz_path c') by (eapply rz_path_star; [exists T; exact H | exact Hstar]).
destruct Hp as [T' HT']. exact (realizes_no_sserror c' T' evs HT' Herr).
Qed.
Lemma t_alt_unit : ltac2:(TCodec.tc2 tcn__ShapeAlg ";'B&S:p021&SF&SCr1%2261(A%311%6231pY<81").
Proof.
intros f tr. split; [intros [[] Hf]; exact Hf | intro Hf; exists tt; exact Hf].
Qed.
Lemma rz_silent1 : ltac2:(TCodec.tc2 tcn__ShapeAlg "E'QC&S:&S<r3'B(<'R7%211q041q056%847621'S>r2%22:1r5%421<p031p071pX4A1pXLC1pXJD1").
Proof.
intros c c' T Hnode Hc.
apply (rz_conseq c (t_alt (fun _ : unit => t_emit [] T))).
- apply (rz_node c unit (fun _ => []) (fun _ => c') (fun _ => T) tt Hnode).
intros []; exact Hc.
- eapply t_eq_trans;
[ apply (t_alt_unit (fun _ : unit => t_emit [] T))
| apply t_emit_nil_eq; eapply realizes_nonempty; exact Hc ].
Qed.
Lemma rz_emit1 : ltac2:(TCodec.tc2 tcn__ShapeAlg "I'QC':'R7%211&S:&S<r4'Br3q021q034%645421'S>r2%2281r6&SE%12;9%6231p051p091pX4A1pY6C1pXLG1pXJH1").
Proof.
intros c c' e T Hnode Hc.
apply (rz_conseq c (t_alt (fun _ : unit => t_emit e T))).
- apply (rz_node c unit (fun _ => e) (fun _ => c') (fun _ => T) tt Hnode).
intros []; exact Hc.
- apply t_alt_unit.
Qed.
Lemma rz_alt2 : forall c (IA IB : Type) (nx : IA + IB -> config) (A B : TSet)
(a0 : IA) (b0 : IB),
node_ok c (IA + IB) (fun _ => []) nx ->
(forall i, realizes (nx (inl i)) A) ->
(forall i, realizes (nx (inr i)) B) ->
realizes c (t_alt2 A B).
Proof.
intros c IA IB nx A B a0 b0 Hnode HA HB.
assert (HA0 : A []) by (eapply realizes_nonempty; apply (HA a0)).
assert (HB0 : B []) by (eapply realizes_nonempty; apply (HB b0)).
apply (rz_conseq c
(t_alt (fun i : IA + IB =>
t_emit [] (match i with inl _ => A | inr _ => B end)))).
- apply (rz_node c (IA + IB) (fun _ => []) nx
(fun i => match i with inl _ => A | inr _ => B end) (inl a0) Hnode).
intros [i|i]; [apply HA | apply HB].
- intro tr. unfold t_alt2. split.
+ intros [[i|i] Hi];
[ left; exact (proj1 (t_emit_nil_eq A HA0 tr) Hi)
| right; exact (proj1 (t_emit_nil_eq B HB0 tr) Hi) ].
+ intros [H | H];
[ exists (inl a0); exact (proj2 (t_emit_nil_eq A HA0 tr) H)
| exists (inr b0); exact (proj2 (t_emit_nil_eq B HB0 tr) H) ].
Qed.
Lemma rz_cases1 : forall c (I : Type) (nx : I -> config) (T : TSet) (i0 : I),
node_ok c I (fun _ => []) nx ->
(forall i, realizes (nx i) T) ->
realizes c T.
Proof.
intros c I nx T i0 Hnode Hc.
assert (HT0 : T []) by (eapply realizes_nonempty; apply (Hc i0)).
apply (rz_conseq c (t_alt (fun _ : I => t_emit [] T))).
- apply (rz_node c I (fun _ => []) nx (fun _ => T) i0 Hnode). exact Hc.
- intro tr. split.
+ intros [i Hi]. exact (proj1 (t_emit_nil_eq T HT0 tr) Hi).
+ intros Ht. exists i0. exact (proj2 (t_emit_nil_eq T HT0 tr) Ht).
Qed.
Lemma sstep_cfg_svc_cases : ltac2:(TCodec.tc2 tcn__ShapeAlg "T0'Q8'R3'U6yR0%211':'R7%211'QM'D'=%117&Q;r5%211(4r3%22=1%93741'QKvU3vU2(QEr6%221;r2%75652:1'H'E'R4'C&QO&QNr:r8%33?21r9(Q4r1%24:G>1%93541&G&QJ%14F87K%311&R9%11E(2%11Q<%Q83Q631%Q93Q;@I%Q91QB&R;&R>r4%211%42Q81%Q:2QHC%QA3721r7(Q?&Q@&QAr;%221:%411%Q<21L%711%QK3QL91%Q72;1%Q82D1qYLR61%Q<2R71(<%11R4%R23R4@1%G1QL%I2QD1%O1R=%R63L21(Q>%R83R9QJ1%QD231%QE281%QI2<1%QG2Q41%QH2Q:1%Q:1R7%R92RDQB%R@3R>21&5(7&S@%12R=QG%33RH1D%53RIR61%RG3RIQN1%R;2Q2RA%Q611%RJ3RKQ81%R6241%R72<1qY2S21%R;2S31%R=2B1%R;2R11qY:S31%R?2S41qYJS;1%RA2S<1qY8RA1%RC2RB1%R@3RLQES3(Q5%11RE%RD33RL1%S;3S=QNQ:%S<3S=S5Q5%RH221%RI241%RM291p0RO1p0S81pZ:SC1pY6SE1pZJSI1pYHSM1pYNSO1").
Proof.
intros ms model x8 e st Hsvc Hss.
inversion Hss; subst; try congruence;
match goal with H : ms_svc_pending ms = Some ?y |- _ =>
rewrite Hsvc in H; injection H as -> end.
-
left. eexists _, _, _. split; [eassumption|]. left.
split; [assumption|]. split; [assumption|]. left. eexists. repeat split; eauto.
-
left. eexists _, _, _. split; [eassumption|]. left.
split; [assumption|]. split; [assumption|]. right. repeat split; auto.
-
left. eexists _, _, _. split; [eassumption|]. right.
eexists. split; [eassumption|]. split; [|reflexivity].
unfold halt_ev. match goal with Hk : m_killed _ = None |- _ => rewrite Hk end. reflexivity.
-
left. eexists _, _, _. split; [eassumption|]. right.
match goal with Hk : m_killed ?mm = Some _ |- _ =>
destruct (m_halted mm) as [code|] eqn:Hhc;
[| rewrite (m_killed_of_m_halted_none _ Hhc) in Hk; discriminate Hk];
exists code; split; [reflexivity | split; [unfold halt_ev; rewrite Hk; reflexivity | reflexivity]]
end.
-
right. repeat split; auto.
Qed.
Lemma node_svc : forall ms model x8 (I : Type)
(effs : I -> SyscallEffect) (ms' : I -> Model) (evs : I -> list event),
m_halted model = None ->
ms_svc_pending ms = Some x8 ->
(forall i, syscall_spec (sys_input segs ms x8) model (Ok (effs i) (ms' i) (evs i))) ->
(forall i, ~ spurious_refusal_cfg scfg (sys_input segs ms x8) model (effs i)) ->
(forall eff m' ev, syscall_spec (sys_input segs ms x8) model (Ok eff m' ev) ->
(exists i, eff = effs i /\ m' = ms' i /\ ev = evs i)
\/ (spurious_refusal_cfg scfg (sys_input segs ms x8) model eff /\ m_halted m' = None)) ->
~ syscall_spec (sys_input segs ms x8) model Unmodeled ->
(forall i, m_halted (ms' i) = None) ->
(forall i, m_vm_lazy (ms' i) = []) ->
node_ok (mkCfg ms model) I evs
(fun i => mkCfg (advance_past_svc (apply_effect ms (effs i))) (ms' i)).
Proof.
intros ms model x8 I effs ms' evs Hh Hsvc Hok Hns Hinv Hnu Hh' Hlazy. split.
- intros i.
apply (sstep_cfg_syscall segs scfg ms model x8 (effs i) (ms' i) (ms' i) (evs i) Hh Hsvc
(Hok i) (Hns i) (Hh' i)).
apply materialize_model_accesses_no_lazy. exact (Hlazy i).
- intros e st Hss.
destruct (sstep_cfg_svc_cases ms model x8 e st Hsvc Hss)
as [(eff & model' & ev & Hspec &
[(Hnsp & Hh2 & [(m'' & -> & Hmat & ->) | (-> & Hmat & ->)]) | (code & Hh2 & -> & ->)])
| (Hum & -> & ->)].
+ destruct (Hinv _ _ _ Hspec) as [(i & -> & -> & ->) | [Hsp _]]; [| exfalso; exact (Hnsp Hsp)].
rewrite (materialize_model_accesses_no_lazy _ _ (Hlazy i)) in Hmat.
injection Hmat as <-. exists i. split; reflexivity.
+ destruct (Hinv _ _ _ Hspec) as [(i & -> & -> & ->) | [Hsp _]]; [| exfalso; exact (Hnsp Hsp)].
rewrite (materialize_model_accesses_no_lazy _ _ (Hlazy i)) in Hmat. discriminate.
+ destruct (Hinv _ _ _ Hspec) as [(i & -> & -> & ->) | [_ Hh3]];
[rewrite Hh' in Hh2; discriminate | rewrite Hh3 in Hh2; discriminate].
+ exfalso. exact (Hnu Hum).
Qed.
Lemma node_svc_on : forall ms model x8 (I : Type)
(effs : I -> SyscallEffect) (ms' : I -> Model) (evs : I -> list event),
m_halted model = None ->
ms_svc_pending ms = Some x8 ->
injected_family_off scfg (sys_input segs ms x8) = false ->
(forall i, syscall_spec (sys_input segs ms x8) model (Ok (effs i) (ms' i) (evs i))) ->
(forall eff m' ev, syscall_spec (sys_input segs ms x8) model (Ok eff m' ev) ->
exists i, eff = effs i /\ m' = ms' i /\ ev = evs i) ->
~ syscall_spec (sys_input segs ms x8) model Unmodeled ->
(forall i, m_halted (ms' i) = None) ->
(forall i, m_vm_lazy (ms' i) = []) ->
node_ok (mkCfg ms model) I evs
(fun i => mkCfg (advance_past_svc (apply_effect ms (effs i))) (ms' i)).
Proof.
intros ms model x8 I effs ms' evs Hh Hsvc Hon Hok Hinv Hnu Hh' Hlazy.
apply (node_svc ms model x8 I effs ms' evs Hh Hsvc Hok); try assumption.
- intros i. apply not_spurious_on. exact Hon.
- intros eff m' ev Hs. left. exact (Hinv eff m' ev Hs).
Qed.
Lemma pnode_instr : ltac2:(TCodec.tc2 tcn__ShapeAlg "QH'Q8'R3'D'='U6yR0%211%411&R9r2%211(2%116%;3631':'?%12::%311&R:r3%211(<%116%E3631&Q;r5%211%I3D1?'Q7%11M&Q=vU3r6%3221(Q6r4%22Q41%Q33841&S=(QEr7%2219'B'R7%G11q031%72>6q051%:47631p0<1p0G1p0L1p0Q71pZ0QE1pYHQE1pYNQG1").
Proof.
intros ms model ms' Hh Hlazy Hsvc Hstep. split.
- intros []. apply (sstep_instr segs ms model ms' model);
[assumption | assumption |].
rewrite (mi_account_step_no_lazy segs ms model Hlazy), Hstep. reflexivity.
- intros e st Hss.
destruct (sstep_instr_inv segs ms model ms' e st Hlazy Hsvc Hstep Hss) as [-> ->].
exists tt. split; reflexivity.
Qed.
Lemma node_instr : ltac2:(TCodec.tc2 tcn__ShapeAlg "QH'Q8'R3'D'='U6yR0%211%411&R9r2%211(2%116%;3631':'?%12::%311&R:r3%211(<%116%E3631&Q;r5%211%I3D1?'Q7%11M&Q=vU3r6%3221(Q6r4%22Q41%Q33841&S<(QEr7%2219'B'R7%G11q031%72>6q051%:47631p0<1p0G1p0L1p0Q71pZ0QE1pYHQE1pYNQG1").
Proof.
intros ms model ms' Hh Hlazy Hsvc Hstep.
apply node_ok_of_pnode_instr; [exact Hsvc | apply pnode_instr; assumption].
Qed.
Lemma rz_step : ltac2:(TCodec.tc2 tcn__ShapeAlg "QH'Q8'R3&S:'D'='U6yR0%211%411&R9r3%211(2%116%;3631':'?%12::%311&R:r4%211(<%116%E3631&Q;r6%211%I3D1?'Q7%11N&Q=vU3r7%3221(Q6r5%22Q51%Q33841'S>(QE%12?8%3216r9r8%5221%721Dp051p0:1p0E1p0J1p0Q51pX4QB1pZ0QE1pYHQE1pYNQG1").
Proof.
intros ms model ms' T Hh Hlazy Hsvc Hstep Hc.
eapply rz_silent1; [apply node_instr; eassumption | exact Hc].
Qed.
Lemma rz_msteps : ltac2:(TCodec.tc2 tcn__ShapeAlg "Q>'Q8'R3&S:'D'='U6yR0%211%411&R9r2%211(2%116%;3631':'?%12::%311&R:r3%211(<%116%E3631'RFvU3r6r5%43321'S>(QE%1254r4%4221r8%5219%7219p041p0:1p0@1p0K1pX4Q81pYHQ:1pZ0Q<1pYNQ=1").
Proof.
intros ms ms' model T Hh Hlazy Hms;
induction Hms as [ms | ms ms1 ms2 Hsvc Hstep Hms IH];
intro Hc; [exact Hc|].
eapply rz_step; [exact Hh | exact Hlazy | exact Hsvc | exact Hstep
| apply IH; exact Hc].
Qed.
Lemma pnode_write1 : ltac2:(TCodec.tc2 tcn__ShapeAlg "SD'Q8'R3'U6yR0%211':y8%511%311'D'=%117&R9r3%211(2%11<%83631'?%12??%?11&R:r4%211(<%116%A3631&RDr5%211&Q;r7%211(4%12N6%J3H31'Q0&U8r6%22Q41+R0%Q03521&Q9r9(3%3221&U5+1%22Q=1%Q83Q=41%Q81Q:&Q:r:u1%<221u2%>241%63531%I2QBK%QB3921&RBr8%211'I&9%12QJF%32=1&S=(QEr=r<%3221&SL%11E&N'R7(R5%11M&M&J';'Cr1%D2N1%D2R=>%F231%5231qZ271%93816r;%<3RC21%A4RD@>1qYDC1&Q@&Q<r>&Q1%12RJ7%4231%611%Q021OqYDL1%Q34OM:1p0Q51p0Q:1p0Q>1p0QI1p0R21p0R91p0R@1p0RD1p0RN1pXFS81pZJS=1pYHSA1pYNSC1").
Proof.
intros ms model x8 buf Hh Hlazy Hfd Hsvc Hno Hg Hr Hbm Hnb. split.
- intros [n [Hn1 Hn2]]. cbn [proj1_sig].
rewrite <- (apply_effect_copyins_no_write ms (len_word (firstn n buf))
[(ms_gpr ms 1, n)]).
apply (sstep_syscall segs ms model x8
(with_copyins [(ms_gpr ms 1, n)]
(mkEffect (len_word (firstn n buf)) [] [])) model
model (map (WriteEv (Z_to_bv 64 1)) (firstn n buf))).
+ exact Hh.
+ exact Hsvc.
+ apply write1_ok_n; assumption.
+ exact Hh.
+ apply materialize_model_accesses_no_lazy. exact Hlazy.
- intros e st Hss.
destruct (sstep_write_inv segs ms model x8 buf e st
Hh Hlazy Hfd Hsvc Hno Hg Hr Hbm Hnb Hss)
as (n & Hn1 & Hn2 & -> & ->).
exists (exist _ n (conj Hn1 Hn2)). split; reflexivity.
Qed.
Lemma node_write1 : ltac2:(TCodec.tc2 tcn__ShapeAlg "SD'Q8'R3'U6yR0%211':y8%511%311'D'=%117&R9r3%211(2%11<%83631'?%12??%?11&R:r4%211(<%116%A3631&RDr5%211&Q;r7%211(4%12N6%J3H31'Q0&U8r6%22Q41+R0%Q03521&Q9r9(3%3221&U5+1%22Q=1%Q83Q=41%Q81Q:&Q:r:u1%<221u2%>241%63531%I2QBK%QB3921&RBr8%211'I&9%12QJF%32=1&S<(QEr=r<%3221&SL%11E&N'R7(R5%11M&M&J';'Cr1%D2N1%D2R=>%F231%5231qZ271%93816r;%<3RC21%A4RD@>1qYDC1&Q@&Q<r>&Q1%12RJ7%4231%611%Q021OqYDL1%Q34OM:1p0Q51p0Q:1p0Q>1p0QI1p0R21p0R91p0R@1p0RD1p0RN1pXFS81pZJS=1pYHSA1pYNSC1").
Proof.
intros ms model x8 buf Hh Hlazy Hfd Hsvc Hno Hg Hr Hbm Hnb.
apply (node_ok_of_pnode_sysno ms model x8 64%Z); [exact Hsvc | exact Hno | exact injected_arm_64 |].
apply (pnode_write1 ms model x8 buf); assumption.
Qed.
Lemma rz_write1 : ltac2:(TCodec.tc2 tcn__ShapeAlg "SC'Q8'R3'U6yR0%211':y8%511%311&S:'D'=%118&R9r4%211(2%11=%83631'?%12@@%@11&R:r5%211(<%116%A3631&RDr6%211&Q;r8%211(4%12O6%J3H31'Q0&U8r7%22Q51+R0%Q03521&Q9r:(3%3221&U5+1%22Q>1%Q83Q>41%Q81Q;&Q:r;u1%<221u2%>241%63531%I2QCK%QB3921&RBr9%211'I&9%12QKF%32=1';r1%62@1r2r=%82R21%:231'S>(QE&Q@&Q<rA&Q1&Mr3r>%33R=21%52R>1%8271%:11r@%=221%?21Bp0A1p0F1pZ2I1r?%C21<&SHr<%23QA1Q=%H241p071p0Q21p0Q71p0Q;1p0QF1p0QO1p0R61p0R=1p0RA1p0RK1pX4S51pXFS71pZJS<1pYHS@1pYNSB1").
Proof.
intros ms model x8 buf T Hh Hlazy Hfd Hsvc Hno Hg Hr Hbm Hnb Hc.
unfold t_write_ch.
apply (rz_node (mkCfg ms model) (wr_index buf)
(fun i => map (WriteEv (Z_to_bv 64 1)) (firstn (proj1_sig i) buf))
(fun i => mkCfg (advance_past_svc
(set_gpr0 ms (len_word (firstn (proj1_sig i) buf))))
model)
(fun _ => T) (wr_full buf Hnb)).
- apply (node_write1 ms model x8 buf); assumption.
- intros [n [Hn1 Hn2]]. cbn [proj1_sig]. apply Hc; assumption.
Qed.
Lemma node_exit : ltac2:(TCodec.tc2 tcn__ShapeAlg "QK'Q8'R3'U6yR0%211'D'=%113&R9r2%211(2%118%83631&Q;r4%211(4%12>9%>3<31&RLr3%211&S<(QEr6r5%3221'B(7'R7(R1&U7&Q9r7(3%3221&U5+WO%22Q41%83Q541&R8%11A%<231(<%11?%A3@31q0C1&R?%129H%J2@1q0G1%M4IH51p0O1p0Q31p0Q:1pZJQD1pYHQH1pYNQJ1").
Proof.
intros ms model x8 Hh Hsvc Hx8.
set (code := bv_and (ms_gpr ms 0) (Z_to_bv 64 255)).
split.
- intros []. cbn.
replace [ExitEv code (m_fs model)]
with ([] ++ [ExitEv code (m_fs (with_halted code model))]) by reflexivity.
apply (sstep_cfg_exit segs scfg ms model x8 (mkEffect (Z_to_bv 64 0) [] [])
(with_halted code model) [] code);
[exact Hh | exact Hsvc
| apply (exit_dispatch_ok (sys_input segs ms x8) model);
rewrite in_sysno_sys_input; exact Hx8
| reflexivity
| apply m_killed_with_halted ].
- intros e st Hss.
destruct (sstep_exit_inv segs ms model x8 e st Hh Hsvc Hx8 (sstep_cfg_sub _ _ _ _ _ Hss))
as [-> ->].
exists tt. split; reflexivity.
Qed.
Lemma rz_exit : ltac2:(TCodec.tc2 tcn__ShapeAlg "Q?'Q8'R3'U6yR0%211'D'=%113&R9r2%211(2%118%83631&Q;r4%211(4%12>9%>3<31&RLr3%211'S>(QEr6r5%3221&SG&U7&Q9(3%2271&U5+WO%22Q01%73Q141&R8%11<%;231%A2=1p0C1p0G1p0N1pZJQ81pYHQ<1pYNQ>1").
Proof.
intros ms model x8 Hh Hsvc Hx8.
unfold t_exit.
eapply (rz_emit1 (mkCfg ms model)
(mkCfg ms (with_halted (bv_and (ms_gpr ms 0) (Z_to_bv 64 255)) model))).
- apply (node_exit ms model x8); assumption.
- apply rz_halt. cbn. discriminate.
Qed.
Lemma node_munmap : ltac2:(TCodec.tc2 tcn__ShapeAlg "R;'Q8'R3'U6yR0%211'D'=%113&R9r2%211(2%118%83631':'?%12<<%311&R:r3%211(<%116%B3631&Q;r5%211(4%12H9%H3F31'Q0&U8r4%22N1+VG%N3521&S0r7r6%3221&S<(QEr8%2216'B'R7%I11q031&Q@&QAr9&S1%112%4231%611&S2&Q9(3%2281&S3u1%52;1%311%8351E%G2:1q0E1%J4GFC1p0L1p0Q11p0Q81p0Q?1p0QJ1pZJR41pYHR81pYNR:1").
Proof.
intros ms model x8 Hh Hlazy Hsvc Hno Hargs.
apply (node_ok_of_pnode_sysno ms model x8 215%Z); [exact Hsvc | exact Hno | exact injected_arm_215 |].
split.
- intros []. apply (sstep_syscall segs ms model x8 (munmap_eff ms)
(munmap_model (ms_gpr ms 0) (page_round_up (ms_gpr ms 1)) model)
(munmap_model (ms_gpr ms 0) (page_round_up (ms_gpr ms 1)) model) []).
+ exact Hh.
+ exact Hsvc.
+ apply munmap_ok; assumption.
+ rewrite munmap_model_halted; exact Hh.
+ apply materialize_model_accesses_no_lazy.
exact (munmap_model_no_lazy _ _ _ Hlazy).
- intros e st Hss.
destruct (sstep_munmap_inv segs ms model x8 e st Hh Hlazy Hsvc Hno Hargs Hss)
as [-> ->].
exists tt. split; reflexivity.
Qed.
Lemma rz_munmap : ltac2:(TCodec.tc2 tcn__ShapeAlg "R:'Q8'R3'U6yR0%211&S:'D'=%114&R9r3%211(2%119%83631':'?%12==%311&R:r4%211(<%116%B3631&Q;r6%211(4%12I9%H3F31'Q0&U8r5%22O1+VG%N3521&S0r8r7%3221'S>(QE&Q@&QAr9&S1%112%4231%611&S2&Q9(3%2281&S3u1%52;1%311%8351D%A2:1%C21Q2r:%D21A%F21Hp041p0I1p0N1p0Q51p0Q<1p0QG1pX4R11pZJR31pYHR71pYNR91").
Proof.
intros ms model x8 T Hh Hlazy Hsvc Hno Hargs Hc.
eapply rz_silent1; [apply (node_munmap ms model x8); assumption | exact Hc].
Qed.
Definition mmap_grant_eff (ms : machine_state) (a : word) : SyscallEffect :=
mkEffect a [] [(a, page_round_up (ms_gpr ms 1))].
Lemma mmap_grant_not_refusal : ltac2:(TCodec.tc2 tcn__ShapeAlg "Q:'Q8'U6yR0%211'R3'D'Q0&U8r3%2271+VN%63521'6&RM&Q9r5(3%3221r2&R=u1%7261%?2D1%411%;47@61(@%E3>21&QH&QNvU3r6%3321@r4%6321I(8%N3G21p0:1p0J1pX>Q31pYHQ31pZJQ51pYNQ91").
Proof.
intros ms x8 model a Hno Hg.
rewrite (refusal_b_mmap (sys_input segs ms x8) model a) by (rewrite in_sysno_sys_input; exact Hno).
pose proof (grant_not_errno (ms_gpr ms 0) model a _
(page_round_up_Z_nonneg _ (proj1 (bv_unsigned_in_range 64 (ms_gpr ms 1)))) Hg) as Hne.
unfold errno_ret_in, mmap_errnos in Hne. cbn [existsb] in Hne.
rewrite orb_false_r in Hne. exact Hne.
Qed.
Lemma node_mmap : ltac2:(TCodec.tc2 tcn__ShapeAlg "S@'Q8'R3'U6yR0%211'D'=%113&R9r2%211(2%118%83631':'?%12<<%311&R:r3%211(<%116%B3631&Q;r5%211(4%12H9%H3F31'Q0&U8r4%22N1+VN%N3521&RNr7%211'6&QIvU2%211(8%Q73521'E&RM&Q9r:(3%3221r9r1&R=u1%8271%I2QE1%411%<48761(@%QG3E21qX>QI1%A2QJ1&S<(QE%12A>'Kr;%E21C%F22?%Q72R31%B11%J44HD1%R43Q21>qX>R61%92R71'R7%QH11q031&Q@&QA&S;&Jr<%Q521Q3%Q622O%QG2RC1%Q211%Q:44EQ41%RD3QB1NqX>RF1%93RG1Q7%;2I1%=2J1%?11&RO&S3%11L%3371QB%Q3251qYDI1%Q64Q4JG1p0Q81p0QK1p0R21p0R61p0R=1p0RD1p0RO1pZJS91pYHS=1pYNS?1").
Proof.
intros ms model x8 Hh Hlazy Hsvc Hno Hargs Halloc [a0 Ha0].
set (nZ := page_round_up_Z (bv_unsigned (ms_gpr ms 1))) in *.
set (n := page_round_up (ms_gpr ms 1)) in *.
apply (node_svc ms model x8 {a : word | grant_ok (ms_gpr ms 0) model a nZ = true}
(fun i => mmap_grant_eff ms (proj1_sig i))
(fun i => mmap_model (proj1_sig i) n model)
(fun _ => []) Hh Hsvc).
- intros [a Ha]. cbn [proj1_sig]. unfold mmap_grant_eff. apply mmap_succ_ok; assumption.
- intros [a Ha]. cbn [proj1_sig]. apply not_spurious_nonrefusal.
unfold mmap_grant_eff. cbn [eff_ret]. eapply mmap_grant_not_refusal; eassumption.
- intros eff m' ev Hspec.
destruct (mmap_ok_inv segs ms x8 model eff m' ev Hno Hargs Hspec)
as [-> [(e & He & -> & ->) | (a & Ha & -> & ->)]].
+ right. split; [| exact Hh].
apply (spurious_intro scfg (sys_input segs ms x8) model _ (mmap_grant_eff ms a0)
(mmap_model a0 n model) []).
* rewrite (injected_family_off_alloc scfg _ 222%Z); [rewrite Halloc; reflexivity | | auto].
rewrite in_sysno_sys_input. exact Hno.
* cbn [eff_ret]. rewrite (refusal_b_mmap (sys_input segs ms x8))
by (rewrite in_sysno_sys_input; exact Hno).
unfold mmap_errnos in He. destruct He as [<- | []]. apply bv_eqb_refl.
* unfold mmap_grant_eff. apply mmap_succ_ok; assumption.
* cbn [eff_ret]. eapply mmap_grant_not_refusal; eassumption.
+ left. exists (exist _ a Ha). cbn [proj1_sig]. repeat split; reflexivity.
- apply mmap_no_unmodeled; assumption.
- intros [a Ha]. cbn [proj1_sig]. rewrite mmap_model_halted. exact Hh.
- intros [a Ha]. cbn [proj1_sig]. exact (eq_trans (mmap_model_lazy _ _ _) Hlazy).
Qed.
Lemma rz_mmap : ltac2:(TCodec.tc2 tcn__ShapeAlg "SE'Q8'R3'U6yR0%211&S:'D'=%114&R9r3%211(2%119%83631':'?%12==%311&R:r4%211(<%116%B3631&Q;r6%211(4%12I9%H3F31'Q0&U8r5%22O1+VN%N3521&RNr8%211'6&QIvU2%211(8%Q73521&RM&Q9r;(3%3221r:r1&R=u1%8271%H2QE1%411%<48761(@%QF3D21'S>(QE&Q@&QAr<(R<r2y8%R311%QG11%QG2R31%QB11(7(>&S3%M2;F%211%44R:R:;1%63QN1QH'R2%QK11';%R32R?1%QN11%C6B=6QN41%F2E1%H11&RO%13F<Q9%L231r9%O221p0Q11pX>RJ1'E%QA2OQ?%R12RNE%Q=11%QE43QCQ?1%RN3QL1Q9qX>S11%72S21%Q92Q6QG%Q;21=p031p0<1p0QN1p0R51p0R91p0R@1p0RG1p0S21p4S<1pZJS>1pYHSB1pYNSD1").
Proof.
intros ms model x8 B Hh Hlazy Hsvc Hno Hargs Halloc HB Hex.
destruct Hex as [a0 Ha0].
apply (rz_cases1 (mkCfg ms model) _ _ B (exist _ a0 Ha0)
(node_mmap ms model x8 Hh Hlazy Hsvc Hno Hargs Halloc (ex_intro _ a0 Ha0))).
intros [a Ha]. cbn [proj1_sig]. apply HB. exact Ha.
Qed.
Lemma node_mmap_nogrant : ltac2:(TCodec.tc2 tcn__ShapeAlg "RC'Q8'R3'U6yR0%211'D'=%113&R9r2%211(2%118%83631':'?%12<<%311&R:r3%211(<%116%B3631&Q;r5%211(4%12H9%H3F31'Q0&U8r4%22N1+VN%N3521&RNr7%211'6&RM&Q9r9(3%3221r8r1&R=u1%8271%C2Q?1%411%<48761(8%QA3?21pX>QC1&S<(QE%12@='B'R7%Q811q031&Q@&Q<r:&R6&R0%211%5241%711%>21Mq0=1%A4?>;1p0C1p0Q51p0Q91p0Q@1p0QG1p0R21pZJR<1pYHR@1pYNRB1").
Proof.
intros ms model x8 Hh Hlazy Hsvc Hno Hargs Hnone.
rewrite <- (apply_effect_no_write ms (errno_ret ENOMEM)).
apply (node_svc ms model x8 unit (fun _ => mkEffect (errno_ret ENOMEM) [] [])
(fun _ => model) (fun _ => []) Hh Hsvc).
- intros []. apply mmap_fail_ok; [assumption | assumption | apply ENOMEM_in_mmap_errnos].
- intros []. apply not_spurious_forced. intros eff' m' evs' Hspec.
destruct (mmap_ok_inv segs ms x8 model eff' m' evs' Hno Hargs Hspec)
as [-> [(e & He & -> & ->) | (a & Ha & -> & ->)]].
+ cbn [eff_ret]. rewrite (refusal_b_mmap (sys_input segs ms x8))
by (rewrite in_sysno_sys_input; exact Hno).
unfold mmap_errnos in He. destruct He as [<- | []]. apply bv_eqb_refl.
+ rewrite Hnone in Ha. discriminate Ha.
- intros eff m' ev Hspec. left.
destruct (mmap_ok_inv segs ms x8 model eff m' ev Hno Hargs Hspec)
as [-> [(e & He & -> & ->) | (a & Ha & -> & ->)]].
+ exists tt. unfold mmap_errnos in He. destruct He as [<- | []]. repeat split; reflexivity.
+ rewrite Hnone in Ha. discriminate Ha.
- apply mmap_no_unmodeled; assumption.
- intros []. exact Hh.
- intros []. exact Hlazy.
Qed.
Lemma rz_mmap_nogrant : ltac2:(TCodec.tc2 tcn__ShapeAlg "RC'Q8'R3'U6yR0%211&S:'D'=%114&R9r3%211(2%119%83631':'?%12==%311&R:r4%211(<%116%B3631&Q;r6%211(4%12I9%H3F31'Q0&U8r5%22O1+VN%N3521&RNr8%211'6&RM&Q9r:(3%3221r9r1&R=u1%8271%C2Q@1%411%<48761(8%QA3?21pX>QD1'S>(QE&Q@&Q<&R6&R0%211%42E1%611%821Dr7%;221r;%<21K%>21Q1p041p0A1p0Q31p0Q71p0Q>1p0QE1p0R01p2R:1pZJR<1pYHR@1pYNRB1").
Proof.
intros ms model x8 A Hh Hlazy Hsvc Hno Hargs Hnone HA.
eapply rz_silent1; [apply (node_mmap_nogrant ms model x8); assumption | exact HA].
Qed.
End WithSegs.
Section Bridges.
Variable scfg : SpuriousCfg.
Lemma cat_realizes : ltac2:(TCodec.tc2 tcn__ShapeAlg "QO':'Q3%211'Q8'R3'U6y8%211%811%911yR0%611'D'=%113&R9r3%211(2%118%83631'?%12;;%G11&R:r4%211(<%116%A3631&RDr5%211'RGr8r7%34215;&RCr6%211'SBr:vU2(QEr9%221;&SK&SG&R8%11?%32<1%52@1%<4;:71p0>1p0B1p0G1p0K1p0Q51pY2Q?1pXHQB1pYHQH1pYNQJ1pZ8QL1").
Proof.
intros segs ms model bufs code Hh Hlazy Hfd Hte. revert model Hh Hlazy Hfd.
induction Hte as
[ms x8 Hsvc Hx8
| ms x8 buf bufs code Hsvc Hno Hg Hr Hnb Hcont IH
| ms ms' bufs code Hsvc Hstep Hte IH];
intros model Hh Hlazy Hfd Hbm.
- rewrite t_writes_pick_nil. eapply rz_exit; eassumption.
- apply Forall_cons_iff in Hbm as [Hb Hbs].
rewrite t_writes_pick_cons. eapply rz_write1; try eassumption.
intros n Hn1 Hn2. apply IH; assumption.
- eapply rz_step; try eassumption. apply IH; assumption.
Qed.
Lemma exitline_realizes_aux : ltac2:(TCodec.tc2 tcn__ShapeAlg "QI':'Q3%211'Q8'U6y8%211%711%811yR0%611'R3'RGr5r4r3r2%544321'D(<%11=%33=71'=%11=&R9%11:(2%11A%:3531'?%12DD%O11&R:%11C%?14%A3421'SBr9vU2(QEr8%221L&SGr6&R8%11Q0%4231%;4:961p0=1p0E1p0M1p0Q21pYHQ91pY2Q;1pXHQ>1pYNQD1pZ8QF1").
Proof.
intros segs ms bufs code model Hte.
induction Hte as
[ms x8 Hsvc Hx8
| ms x8 buf bufs code Hsvc Hno Hg Hr Hnb Hcont IH
| ms ms' bufs code Hsvc Hstep Hte IH]; intros Hbufs Hh;
[| discriminate Hbufs |]; intro Hlazy.
- eapply rz_exit; eassumption.
- eapply rz_step; [exact Hh | exact Hlazy | exact Hsvc | exact Hstep |].
apply IH; [solve [assumption | reflexivity] | exact Hh | exact Hlazy].
Qed.
Lemma exitline_realizes : ltac2:(TCodec.tc2 tcn__ShapeAlg "QD':'Q3%211'Q8'U6yR0%211'R3'RGr4r3(<y8%911%>11%411r2%948721'D'=%11>&R9%116(2%11B%73531'?%12EE%L11&R:%11D%D14%>3421'SBr7vU2(QEr6%221M&SGr5&R8%11Q1%4231%;4:961p0=1p0E1p0N1pYHQ91pY2Q;1pYNQ?1pZ8QA1").
Proof.
intros segs ms code model Hte Hh Hlazy.
exact (exitline_realizes_aux segs ms [] code model Hte eq_refl Hh Hlazy).
Qed.
Lemma rz_wall1_mut : ltac2:(TCodec.tc2 tcn__ShapeAlg "RI':'Q3%211'R3'D'='U6yR0%211%411&R9r1%211(2%116%;3631'?%1299%B11&R:r2%211(<%116%D3631&RDr3%211'C'Q8y8%I11%Q011!p051'SMr8&U5+1%22Q01%5541>DM&RB%11@&S:'R7%G11%Q311r6%11Q5'SBr>vU2(QEr=%22Q21r4%746521p091pZ0M1r<%82H1&SE&N(R5%11Ir7%44Q3F21%621Q9%C4?A81p0;1p0H1pX4L1p0N1p0Q11pYFQ81pZ4Q;1pYNQ?1'SN%15Q:Q7QDQJR3p017pYFQ>1pZ4QA1pYNQE1%QG271p0QI1p0QM1p0R71pYHRD1pZ8RF1").
Proof.
intros segs model Hh Hlazy Hfd.
apply (to_wall_mutind segs (Z_to_bv 64 1)
(fun ms rest k => buf_modeled rest -> forall T : TSet, T [] ->
(forall ms', k ms' -> realizes segs scfg (mkCfg ms' model) T) ->
realizes segs scfg (mkCfg ms model)
(t_emit (map (WriteEv (Z_to_bv 64 1)) rest) T))
(fun ms rest k => buf_modeled rest -> forall T : TSet, T [] ->
(forall ms', k ms' -> realizes segs scfg (mkCfg ms' model) T) ->
realizes segs scfg (mkCfg ms model)
(t_emit (map (WriteEv (Z_to_bv 64 1)) rest) T))).
-
intros ms x8 rest k Hsvc Hno Hg Hr Hnb Hcont IH Hbm T HT Hk.
eapply rz_conseq.
{ apply (rz_node segs scfg (mkCfg ms model) (wr_index rest)
(fun i => map (WriteEv (Z_to_bv 64 1)) (firstn (proj1_sig i) rest))
(fun i => mkCfg (advance_past_svc
(set_gpr0 ms (len_word (firstn (proj1_sig i) rest))))
model)
(fun i => t_emit (map (WriteEv (Z_to_bv 64 1))
(skipn (proj1_sig i) rest)) T)
(wr_full rest Hnb)).
- apply (node_write1 segs scfg ms model x8 rest); assumption.
- intros [n [Hn1 Hn2]]. cbn [proj1_sig].
apply (IH n Hn1 Hn2 (buf_modeled_skipn n rest Hbm) T HT Hk). }
apply t_alt_wall; [exact HT | exact Hnb].
-
intros ms k Hk Hbm T HT Hcont.
eapply rz_conseq; [apply Hcont; exact Hk|].
cbn [map]. apply t_eq_sym. apply t_emit_nil_eq. exact HT.
-
intros ms rest k Hnb Hw IH Hbm T HT Hk. exact (IH Hbm T HT Hk).
-
intros ms ms' rest k Hsvc Hstep Ht IH Hbm T HT Hk.
eapply rz_step; [exact Hh | exact Hlazy | exact Hsvc | exact Hstep
| exact (IH Hbm T HT Hk)].
Qed.
Lemma wall_realizes : ltac2:(TCodec.tc2 tcn__ShapeAlg "R2':'Q3%211'Q8'R3'U6y8%211%811%911yR0%611'D'=%113&R9r3%211(2%118%83631'?%12;;%G11&R:r4%211(<%116%A3631&RDr5%211&SOr8&U5+1%22K1r7%65528>1&RCr6%211'SBr:vU2(QEr9%221>&SI&SG&R8%11B%32<1%52@1%<4;:71p0>1p0B1p0J1p0N1p0Q81pY2QB1pXHQE1pYHQK1pYNQM1pZ8QO1").
Proof.
intros segs ms model bufs code Hh Hlazy Hfd Hw Hbm. revert ms Hw Hbm.
induction bufs as [|buf rest IH]; intros ms Hw Hbm.
- exact (exitline_realizes segs ms code model Hw Hh Hlazy).
- destruct Hw as [Hnb Ht]. apply Forall_cons_iff in Hbm as [Hb Hbs].
rewrite t_writes_cons.
eapply (proj2 (rz_wall1_mut segs model Hh Hlazy Hfd)).
+ exact Ht.
+ exact Hb.
+ unfold t_writes. apply t_writes_ch_exit_has_nil.
+ intros ms' Hk. apply IH; [exact Hk | exact Hbs].
Qed.
Lemma twm_realizes_mut : ltac2:(TCodec.tc2 tcn__ShapeAlg "SB':'Q3%211'C'Q8'R3'U6y8%211%911%:11yR0%611'S4r5r4r3r2r1%6554321'D'=%11:&R9%119(2%11>%73531'?%12AA%N11&R:%11B(<%115%?3531&RDr6%211&RC%113'SBr:vU2(QEr9r8%3221&SIr7&SG&R8%116%32@1%6251%>4=<81p0@1p0C1p0G1p0Q01p0Q91pY2QA1pXHQD1pYHQJ1pYNQL1'S5%16MQDQCQBQAQ@%Q<1QE%Q@3Q>1Q:%Q61Q0%QB3Q81Q4%Q31F&RB%11H%Q31Ir<r;%Q121Q3&SE&N'R7(R5&U5+1%22R91%411%74R>61Q9%Q41Q=%Q62Q71%Q92Q;1%<241%QB4@Q@>1p0B1p0D1p0G1p0I1p0L1p0O1pY2RF1pXHRI1pZ4RK1pYHS01pYNS21'S6%16R3RJRIRHRGRFp019pY2RN1pXHS11pZ4S31pYHS81pYNS:1%S<291%S=2Q@1pZ8S?1").
Proof.
intros segs.
apply (MmapSim.twm_mutind segs
(fun ms model bufs code =>
m_halted model = None -> m_vm_lazy model = [] -> fd1chan model -> bufs_modeled bufs ->
realizes segs scfg (mkCfg ms model) (t_writes bufs (t_exit code (m_fs model))))
(fun ms model rest bufs code =>
m_halted model = None -> m_vm_lazy model = [] -> fd1chan model ->
buf_modeled rest -> bufs_modeled bufs ->
realizes segs scfg (mkCfg ms model)
(t_emit (map (WriteEv (Z_to_bv 64 1)) rest)
(t_writes bufs (t_exit code (m_fs model)))))
(fun ms model rest bufs code =>
m_halted model = None -> m_vm_lazy model = [] -> fd1chan model ->
buf_modeled rest -> bufs_modeled bufs ->
realizes segs scfg (mkCfg ms model)
(t_emit (map (WriteEv (Z_to_bv 64 1)) rest)
(t_writes bufs (t_exit code (m_fs model)))))).
-
intros ms model x8 Hsvc Hx8 Hh Hlazy Hfd Hbm. eapply rz_exit; eassumption.
-
intros ms model buf bufs code Hnb Hp IH Hh Hlazy Hfd Hbm.
apply Forall_cons_iff in Hbm as [Hb Hbs].
rewrite t_writes_cons. exact (IH Hh Hlazy Hfd Hb Hbs).
-
intros ms model x8 bufs code Hsvc Hno Hargs Hte IH Hh Hlazy Hfd Hbm.
eapply rz_munmap; try eassumption.
rewrite <- (munmap_model_fs (ms_gpr ms 0) (page_round_up (ms_gpr ms 1)) model).
apply IH; [rewrite munmap_model_halted; exact Hh
| exact (munmap_model_no_lazy _ _ _ Hlazy)
| apply munmap_model_fd1chan; exact Hfd | exact Hbm].
-
intros ms ms' model bufs code Hsvc Hstep Hte IH Hh Hlazy Hfd Hbm.
eapply rz_step; try eassumption. apply IH; assumption.
-
intros ms model x8 rest bufs code Hsvc Hno Hg Hr Hnb Hcont IH Hh Hlazy Hfd Hbr Hbm.
eapply rz_conseq.
{ apply (rz_node segs scfg (mkCfg ms model) (wr_index rest)
(fun i => map (WriteEv (Z_to_bv 64 1)) (firstn (proj1_sig i) rest))
(fun i => mkCfg (advance_past_svc
(set_gpr0 ms (len_word (firstn (proj1_sig i) rest))))
model)
(fun i => t_emit (map (WriteEv (Z_to_bv 64 1))
(skipn (proj1_sig i) rest))
(t_writes bufs (t_exit code (m_fs model))))
(wr_full rest Hnb)).
- apply (node_write1 segs scfg ms model x8 rest); assumption.
- intros [n [Hn1 Hn2]]. cbn [proj1_sig].
apply (IH n Hn1 Hn2 Hh Hlazy Hfd (buf_modeled_skipn n rest Hbr) Hbm). }
apply t_alt_wall;
[unfold t_writes; apply t_writes_ch_exit_has_nil | exact Hnb].
-
intros ms model bufs code Hte IH Hh Hlazy Hfd Hbr Hbm.
eapply rz_conseq; [apply IH; assumption|].
cbn [map]. apply t_eq_sym. apply t_emit_nil_eq.
unfold t_writes. apply t_writes_ch_exit_has_nil.
-
intros ms model rest bufs code Hnb Hp IH Hh Hlazy Hfd Hbr Hbm.
exact (IH Hh Hlazy Hfd Hbr Hbm).
-
intros ms ms' model rest bufs code Hsvc Hstep Ht IH Hh Hlazy Hfd Hbr Hbm.
eapply rz_step; try eassumption. exact (IH Hh Hlazy Hfd Hbr Hbm).
Qed.
Lemma twm_realizes : ltac2:(TCodec.tc2 tcn__ShapeAlg "QO':'Q3%211'Q8'R3'U6y8%211%811%911yR0%611'D'=%113&R9r3%211(2%118%83631'?%12;;%G11&R:r4%211(<%116%A3631&RDr5%211'S4r8r7r6%453216<&RC%113'SBr:vU2(QEr9%221;&SI&SG&R8%11?%32>1%52@1%<4;:71p0>1p0A1p0G1p0K1p0Q51pY2Q?1pXHQB1pYHQH1pYNQJ1pZ8QL1").
Proof.
intros segs ms model bufs code Hh Hlazy Hfd Hte.
exact (proj1 (twm_realizes_mut segs) ms model bufs code Hte Hh Hlazy Hfd).
Qed.
Definition t_outcomes (fs : Fs.Fs)
(U : (list (list byte) * word) -> Prop) : TSet :=
fun tr => exists o, U o /\ is_prefix tr (AllocSim.outcome_trace fs o).
Lemma t_alt_emit_nil : forall (I : Type) (f : I -> TSet),
(forall i, f i []) -> t_eq (t_alt (fun i => t_emit [] (f i))) (t_alt f).
Proof.
intros I f H tr. split.
- intros [i Hi]. exists i. exact (proj1 (t_emit_nil_eq (f i) (H i) tr) Hi).
- intros [i Hi]. exists i. exact (proj2 (t_emit_nil_eq (f i) (H i) tr) Hi).
Qed.
Lemma t_outcomes_two_alt2 : ltac2:(TCodec.tc2 tcn__ShapeAlg "Q1&Q2':'U6y8%211%411%511yR0%611&SF&S8r5&RAr4r3r2r1%544321%8271&SD&SI&SG%128;%32:1%328=%52:1%7231%B291pY4D1pXDG1pXNF1pXBI1pY@Q01").
Proof.
intros fs bf cf bs cs tr.
unfold t_outcomes, AllocSim2.two_outcomes, AllocSim.outcome_trace, t_alt2.
rewrite !t_writes_exit_iff. split.
- intros (o & [-> | ->] & Hp); cbn [fst snd] in Hp; [left | right]; exact Hp.
- intros [Hp | Hp]; [exists (bf, cf) | exists (bs, cs)]; cbn [fst snd]; auto.
Qed.
Definition t_writes_ch_pick (ch : word) (bufs : list (list byte)) (T : TSet) : TSet :=
fold_right (t_write_ch ch) T bufs.
Lemma t_writes_ch_pick_1 : ltac2:(TCodec.tc2 tcn__ShapeAlg "E':'U6y8%211%411%511&S:'D&S9&U5yR0+1%3221r2r1%73321&SK%1243%;3<31pX4=1pXH?1").
Proof. reflexivity. Qed.
Lemma t_writes_ch_pick_cons : ltac2:(TCodec.tc2 tcn__ShapeAlg "J'U6yR0%211':y8%511%311%411&S:'D&S9r4(7r3r2%33921r1%73621&SH%93853%23971%<3=41pX4>1pXH@1pXFB1pY0G1").
Proof. reflexivity. Qed.
Lemma node_write_ch : ltac2:(TCodec.tc2 tcn__ShapeAlg "SL':'Q3%211'Q8'R3'U6yR0%211y8%411%:11'D'=%116&R9r5%211(2%11;%83631'?%12>>%F11&R:r6%211(<%116%A3631&REr7%237@1&R@%113%G3K14&Q;r:%211(4%12Q0?%M3K31'Q0&U8%12Q5=+R0%Q23421&Q9r<(3%3221%Q73Q;1>%Q71Q9&Q:r=u1%9221u2%;241%63531r8%F2QB1%QB3:31&RBr9%211'I&9%12QJO%32>1&SArAvU2(QEr@r?%3221&SLr;%211&N'R7(R5r>%211&M&J';'Cr1%H2Q31%H2RAQ5%J231%5231qZ271%93816%;3RF1Q@%A4RG@=1qYDC1&Q@&Q<&Q1%12RL6%32Q01%511%Q021OqYDK1%Q56Q4Q3OL91p0Q71p0Q<1p0Q@1p0QL1p0R21p0R81p0R?1p0RC1p0RG1p0S11pXFS;1pZJS?1pY0S@1pY>SA1pYHSE1pYNSG1pZ8SI1").
Proof.
intros segs ms model fd ch x8 buf Hh Hlazy Hfdc H32 Hsvc Hno Hg Hr Hbm Hnb.
apply (node_ok_of_pnode_sysno segs scfg ms model x8 64%Z); [exact Hsvc | exact Hno | exact injected_arm_64 |].
split.
- intros [n [Hn1 Hn2]]. cbn [proj1_sig].
rewrite <- (apply_effect_copyins_no_write ms (len_word (firstn n buf))
[(ms_gpr ms 1, n)]).
apply (sstep_syscall segs ms model x8
(with_copyins [(ms_gpr ms 1, n)]
(mkEffect (len_word (firstn n buf)) [] [])) model
model (map (WriteEv ch) (firstn n buf))).
+ exact Hh.
+ exact Hsvc.
+ eapply write_ch_ok_n; eassumption.
+ exact Hh.
+ apply materialize_model_accesses_no_lazy. exact Hlazy.
- intros e st Hss.
destruct (sstep_write_ch_inv segs fd ch H32 ms model x8 buf e st
Hh Hlazy Hfdc Hsvc Hno Hg Hr Hbm Hnb Hss)
as (n & Hn1 & Hn2 & -> & ->).
exists (exist _ n (conj Hn1 Hn2)). split; reflexivity.
Qed.
Lemma rz_write_ch : ltac2:(TCodec.tc2 tcn__ShapeAlg "SK':'Q3%211'Q8'R3'U6yR0%211y8%411%:11&S:'D'=%117&R9r6%211(2%11<%83631'?%12??%G11&R:r7%211(<%116%A3631&REr8%237@1&R@%113%G3L14&Q;r;%211(4%12Q1?%M3K31'Q0&U8%12Q6=+R0%Q23421&Q9r=(3%3221%Q73Q<1>%Q71Q:&Q:r>u1%9221u2%;241%63531r9%F2QC1%QB3:31&RBr:%211'I&9%12QKO%32>1';r1%62A1r2%72R1D%9221'SBrEvU2(QE&Q@&Q<rD&Q1&Mr3r?%33R>21%52R?1%8271%:11rC%=221%A4@?1Q7p0C1p0G1pZ2J1rBrA%D221&SHr<%23@QF1%K4<I41p081p0Q41p0Q91p0Q=1p0QI1p0QO1p0R51p0R<1p0R@1p0RD1p0RN1pX4S81pXFS:1pZJS>1pY0S?1pY>S@1pYHSD1pYNSF1pZ8SH1").
Proof.
intros segs ms model fd ch x8 buf T Hh Hlazy Hfdc H32 Hsvc Hno Hg Hr Hbm Hnb Hc.
unfold t_write_ch.
apply (rz_node segs scfg (mkCfg ms model) (wr_index buf)
(fun i => map (WriteEv ch) (firstn (proj1_sig i) buf))
(fun i => mkCfg (advance_past_svc
(set_gpr0 ms (len_word (firstn (proj1_sig i) buf))))
model)
(fun _ => T) (wr_full buf Hnb)).
- eapply node_write_ch; eassumption.
- intros [n [Hn1 Hn2]]. cbn [proj1_sig]. apply Hc; assumption.
Qed.
Lemma cat_realizes_ch : ltac2:(TCodec.tc2 tcn__ShapeAlg "R7':'Q3%211'U6yR0%211'Q8'R3y8%611%:11%;11'D'=%119&R9r3%211(2%11>%83631'?%12AA%G11&R:r4%211(<%116%A3631&REr8r7r5%43321&R@r9%211%J3Q112'RHr;r:r6%4532<1:&RC%11='SBr=vU2(QE%129>&S9&SG&R8%11B%32G1%53@I1%;4:971p0=1p0@1p0F1p0K1p0Q11p0Q;1pY2QK1pXHQF1pYHQK1pYNQM1pY0QO1pY>R01pZ8R41").
Proof.
intros segs fd ch ms model bufs code Hh Hlazy Hfdc H32 Hte.
revert model Hh Hlazy Hfdc.
induction Hte as
[ms x8 Hsvc Hx8
| ms x8 buf bufs code Hsvc Hno Hg Hr Hnb Hcont IH
| ms ms' bufs code Hsvc Hstep Hte IH];
intros model Hh Hlazy Hfdc Hbm.
- eapply rz_exit; eassumption.
- apply Forall_cons_iff in Hbm as [Hb Hbs].
rewrite t_writes_ch_pick_cons. eapply rz_write_ch; try eassumption.
intros n Hn1 Hn2. apply IH; assumption.
- eapply rz_step; try eassumption. apply IH; assumption.
Qed.
End Bridges.
