(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)


From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Numbers.BinNums"; "Z"; "@Corelib.Init.Logic"; "and"; "eq"; "or"; "ex"; "not"; "@Corelib.Init.Datatypes"; "prod"; "bool"; "pair"; "list"; "option"; "length"; "nat"; "app"; "true"; "Some"; "false"; "nil"; "cons"; "unit"; "None"; "fst"; "snd"; "tt"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocModel"; "sptr"; "astate"; "kreq"; "region"; "st_regions"; "prid"; "st_init_done"; "free"; "init_state"; "malloc"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocIface"; "ma_s"; "MA"; "ma_blocks"; "ma_L"; "layout_extends"; "MInv"; "ma_owned"; "MA_init"; "free_rel"; "malloc_rel"; "run_init"; "mkMA"; "ri_brk0"; "ri_sec"; "ri_top"; "@Stdlib.ZArith.BinInt.Z"; "le"; "lt"; "add"; "pow"; "modulo"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocInv"; "WF"; "layout"; "ly_ctx"; "user_blocks"; "yields"; "ly_brk0"; "ly_reg"; "ly_sec"; "ly_top"; "Layout"; "bounded"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLayout"; "addr_of"; "byteview_of"; "mc_ctx"; "mconsts"; "topL"; "auxv_ok"; "blocks"; "img_reserved"; "ledger_ok"; "maps_wf"; "mc_chk_guard"; "mc_chk_guard_got"; "mc_ctz_tab"; "mc_libc"; "mc_med_cnt_tab"; "mc_replaced"; "mc_size_classes"; "mc_small_cnt_tab"; "owned"; "statics_ok"; "vm_ok"; "@stdpp.bitvector.definitions"; "bv"; "Z_to_bv"; "@Stdlib.Lists.List"; "In"; "incl"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "VmMaps"; "vm_brk"; "vm_init_sp"; "vm_maps"; "vm_noaccess"; "vm_reserved"; "vm_start_brk"; "@Corelib.Init.Peano"; "lt"; "@Corelib.Lists.ListDef"; "map"; "@LinuxProcessSemantics.Riscv.Prelude"; "bv_eqb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocCalloc"; "calloc_m"; "calloc_overflows"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocFooter"; "reprO"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.NestTier"; "reach_ok"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics State.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc Require Import
  MallocModel MallocInv MallocWfMeta MallocWfMain MallocWfRepr MallocLayout MallocFooter MallocCalloc NestTier.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.

Record MA := mkMA { ma_s : astate ; ma_L : layout }.

Definition ma_blocks (A : MA) : list (Z * Z) := ltac2:(tb__ "0|0|
S47S25VA;A1S22VA;A1A2").
Definition ma_owned (C : mconsts) (A : MA) (a : Z) : Prop := ltac2:(tb__ "0|0|
S53VC;S25VA;A1S22VA;A1Va;A4").

Definition MInv (C : mconsts) (A : MA) (rd : word -> option byte) (wok : word -> bool) (vm : VmMaps) : Prop := ltac2:(tb__ "0|2|
S22VA;A1S19S25VA;A1S37S1S36R2A1S1S40R2A1S1S2S0S38R1A1S43VC;A1A3S1S66R1R2S42Vrd;Vwok;A2M0A3S1S55R1R2Vvm;A3S1S54VC;S42Vrd;S56Q40A1SeL_;A2M1G0A3S1S2S7S1eR2A1S10A3S46VC;R2G1A3F_;S1S49VC;Vvm;A2S1S48VC;Vvm;A2S1S4aVvm;A1S67R2A1A2A2A2A2A2A2A2A2A2A2TL;Ts;").

Record run_init := RI { ri_brk0 : Z; ri_sec : Z; ri_top : Z }.
Definition MA_init (C : mconsts) (ri : run_init) : MA := ltac2:(tb__ "0|0|
S2dS20S3fS43VC;A1ScZ0L_;S2eVri;A1S2fVri;A1S30Vri;A1A5A2").

Lemma MA_init_blocks : ltac2:(tb__ "0|1|
S44S2cS2S9S6S0S0A2M0A1S24S29R2R1A2A1S11G0A1A3Fb;FC;").
Proof. reflexivity. Qed.

Lemma MA_init_WF : ltac2:(tb__ "0|0|
S44S2cS36S22S29R2R1A2A1A1Fb;FC;").
Proof. intros. apply wf_init. Qed.

Definition layout_extends (L L' : layout) (nold : nat) : Prop := ltac2:(tb__ "0|0|
S1S2S0S38VL';A1S38VL;A1A3S1S2S0S3bVL';A1S3bVL;A1A3S1S2S0S3dVL';A1S3dVL;A1A3S1ScS61R1Vnold;A2S2S0S3cVL';R2A2S3cVL;R2A2A3F_;Fr;S2S0S3eVL';A1S3eVL;A1A3A2A2A2A2").

Lemma layout_extends_top : ltac2:(tb__ "0|0|
S37S37ScS26R3R2R1A3S2S0S45R3A1S45R4A1A3F_;Fn;FL';FL;").
Proof. intros L L' n (_ & _ & _ & _ & E). unfold topL. rewrite E. reflexivity. Qed.

Lemma layout_extends_refl : ltac2:(tb__ "0|0|
S37ScS26R2R2R1A3Fn;FL;").
Proof. intros. repeat split; auto. Qed.

Definition malloc_rel (A : MA) (n : Z) (tr : list (kreq * Z)) (res : Z) (A' : MA) : Prop := ltac2:(tb__ "0|4|
S4SaS18A1M0G0S1S3aS6G0S19A2S21Vn;S22VA;A1M1A2Vtr;S8G0S19R1S22VA';A1A4A4S1S26S25VA;A1S25VA';A1M2SbS1bS1cG1A1A2A3S1S2S0Vres;G0S0Lp;R1S18S41G2R1A2Lq;Z0M3Xax2A3S18S2G0R2SfS18R1A2A3S5S2S0S41G2R2A2G3A3A1F_;Fq;A2A2A2Lp;A2").

Definition free_rel (A : MA) (b : Z) (tr : list (kreq * Z)) (A' : MA) : Prop := ltac2:(tb__ "0|3|
S3S1S2S0Vb;Z0A3S1S2S23VA';VA;A3S2S9S6S1aS0A2M0A1Vtr;S11G0A1A3A2A2S4S18S18S4S0S0S1S58S6S18S0A2S8S18S0R2R1A4S39S22VA;A1M1A1A3S1S2S0S41S25VA;A1M2R2A2Vb;A3S1S3aS6S13S19A2S1fSfS18R2A2G1A2Vtr;S8S13S19S17S22VA';A1A4A4S26G2S25VA';A1SbS1bS1cG1A1A2A3A2A2A2Ln;A2Lp;A2A2").

Definition calloc_rel (A : MA) (m n : Z) (tr : list (kreq * Z)) (res : Z) (cleared : bool) (A' : MA) : Prop := ltac2:(tb__ "0|7|
S3S1S2S7S65Vm;Vn;A2M0SeA3S1S2S23VA';VA;A3S1S2S0Vres;Z0M1A3S2S9S6S1aS0A2M2A1Vtr;S11G2A1A3A2A2A2S1S2S7G0S10A3S4SaS6S18S7A2M3A1M4G4S1S3aS6G4S19A2S64Vm;Vn;S22VA;A1M5A3Vtr;S8G4S19R1S22VA';A1A4A4S1S26S25VA;A1S25VA';A1M6SbS1bS1cG5A1A2A3S1S2S0Vres;G4S0Lr;R1G3G3S0Lp;R1S18S7S41G6R2A2Lb;Lq;X6x1Lp;G1Xax2A3S2S7Vcleared;G4S7Lr;R1G3G3S7Lp;R1S18S7R1Lc;Ls;X6x1Lp;S10Xax2A3A2A2A2Lr;A2A2A2").

Lemma user_block_region : ltac2:(tb__ "0|0|
S19S18S0S36R3A1S58S6S18S0A2S8S18S0R3R2A4S39R4A1A3S61S1dR4A1SbS1bS1cR5A1A2A2F_;F_;Fn;Fp;Fs;").
Proof.
  intros s p n HW Hin.
  unfold user_blocks in Hin. apply in_flat_map in Hin as [[g am] [Hg Hin]].
  apply in_flat_map in Hin as [i [Hi Hin]]. cbn in Hin.
  destruct (ss_fr (nth_slot am i)) as [fr|] eqn:Efr. 2:{ destruct Hin. }
  destruct (fr_kind fr). 2:{ destruct Hin. } destruct Hin as [E|[]].
  injection E as E1 E2. subst p.
  destruct (group_in_mapping s g am HW Hg) as (k & o & rg & Em & Hr & _).
  unfold slot_start, padd. rewrite Em. cbn [prid].
  unfold region_of in Hr. apply nth_error_In in Hr. apply In_nth_error in Hr.
  destruct Hr as [j Hj].
  destruct (Nat.lt_ge_cases k (length (st_regions s))) as [Hlt|Hge]; [exact Hlt|].
  exfalso. unfold region_of in *.
  destruct (group_in_mapping s g am HW Hg) as (k' & o' & rg' & Em' & Hr' & _).
  rewrite Em in Em'. injection Em' as <- <-.
  apply nth_error_None in Hge. unfold region_of in Hr'. rewrite Hge in Hr'. discriminate.
Qed.

Lemma addr_of_extends : ltac2:(tb__ "0|0|
S37S37ScS18S26R4R3R2A3S61S1dR2A1R3A2S2S0S41R5R3A2S41R6R3A2A3F_;F_;Fp;Fnold;FL';FL;").
Proof.
  intros L L' nold [r o] (_ & _ & _ & H & _) Hp. unfold addr_of, loc_addr. cbn in Hp. rewrite H by exact Hp. reflexivity.
Qed.

Lemma blocks_extends : ltac2:(tb__ "0|4|
S19S37S37S36R3A1S26R3R2SbS1bS1cR4A1A2A3S9S6S18S0A2M0A1S59G0R1S39R6A1A3S2S9S6S0S0A2M1A1S62G0G1G0S8S0S0S41R6S15S18S0R1A3M2A2S16S18S0R1A3M3A4Lb;R2A4S62G0G1G0S8S0S0S41R7G2A2G3A4Lb;R2A4A3F_;Fl;F_;F_;FL';FL;Fs;").
Proof.
  intros s L L' HW HE l Hincl. induction l as [|[p n] t IH]; [reflexivity|].
  cbn [map fst snd].
  assert (Hp : addr_of L' p = addr_of L p).
  { apply (addr_of_extends L L' (length (st_regions s)) p HE).
    apply (user_block_region s p n HW). apply Hincl. left. reflexivity. }
  rewrite Hp. f_equal. apply IH. intros x Hx. apply Hincl. right. exact Hx.
Qed.

Theorem malloc_rel_blocks : ltac2:(tb__ "0|4|
S23S0S9S6S1aS0A2A1S0S23S36S22R5A1A1S31Z0M0R5A2S2bR7R6R5R4R3A5S3S1S2S0R5G0A3M1S2S9S6S0S0A2M2A1M3S24R4A1S24R8A1A3A2S1S5G1A1S4G3G3S4G3G3S1S2G3S24R6A1SdG2R2S12G2S8S0S0R7R9A4R1A3A3A3S2G3S24RaA1SdG2R2R1A3A3A2Ll2;A2Ll1;A2A2A2F_;F_;F_;FA';Fres;Ftr;Fn;FA;").
Proof.
  intros [s L] n tr res [s' L'] HW Hn (p & Hy & HE & Hres & Hnz). cbn [ma_s ma_L] in *.
  pose proof (malloc_blocks s n tr p s' HW Hn Hy) as HB.
  unfold ma_blocks, blocks. cbn [ma_s ma_L].
  set (F := fun b : sptr * Z => (addr_of L (fst b), snd b)).
  set (F' := fun b : sptr * Z => (addr_of L' (fst b), snd b)).
  destruct p as [q|].
  - right. split; [subst res; apply Hnz; reflexivity|].
    destruct HB as (l1 & l2 & E' & E & _ & _).
    exists (map F' l1), (map F' l2).
    rewrite E', E. rewrite !map_app. cbn [map app]. subst res. split; [reflexivity|].
    subst F F'.
    rewrite (blocks_extends s L L' HW HE l1), (blocks_extends s L L' HW HE l2); try reflexivity.
    + intros x Hx. rewrite E. apply in_app_iff. right. exact Hx.
    + intros x Hx. rewrite E. apply in_app_iff. left. exact Hx.
  - left. split; [exact Hres|]. rewrite HB. subst F F'. apply (blocks_extends s L L' HW HE). intros x Hx; exact Hx.
Qed.

Theorem free_rel_blocks : ltac2:(tb__ "0|3|
S23S0S9S6S1aS0A2A1S23S36S22R4A1A1S2aR5R4R3R2A4S3S1S2S0R5Z0A3S2S9S6S0S0A2M0A1M1S24R3A1S24R6A1M2A3A2S4S0S0S4G1G1S4G1G1S1S2G1S24R9A1SdG0R2S12G0S8S0S0R8R3A4R1A3A3A3S2G1G2SdG0R2R1A3A3A2Ll2;A2Ll1;A2Ln;A2A2F_;F_;FA';Ftr;Fb;FA;").
Proof.
  intros [s L] b tr [s' L'] HW HF. cbn [ma_s ma_L] in *.
  destruct HF as [(Hb & EA & _) | (p & n & Hin & Hb & Hy & HE)].
  - left. injection EA as -> ->. split; [exact Hb | reflexivity].
  - right. pose proof (free_blocks s p n tr s' HW Hin Hy) as (l1 & l2 & E & E').
    set (F := fun b : sptr * Z => (addr_of L (fst b), snd b)).
    set (F' := fun b : sptr * Z => (addr_of L' (fst b), snd b)).
    exists n, (map F l1), (map F l2).
    unfold ma_blocks, blocks. cbn [ma_s ma_L]. fold F F'. rewrite E, E'. rewrite !map_app. cbn [map app].
    subst b. split; [reflexivity|].
    rewrite <- !map_app. subst F F'.
    apply (blocks_extends s L L' HW HE). intros x Hx. rewrite E. apply in_app_iff.
    apply in_app_iff in Hx. destruct Hx; [left; assumption | right; right; assumption].
Qed.

Lemma malloc_rel_WF : ltac2:(tb__ "0|0|
S23S0S9S6S1aS0A2A1S0S23S36S22R5A1A1S31Z0R5A2S2bR7R6R5R4R3A5S36S22R4A1A1F_;F_;F_;FA';Fres;Ftr;Fn;FA;").
Proof. intros A n tr res A' HW Hn (p & Hy & _). exact (malloc_wf _ _ _ _ _ HW Hn Hy). Qed.

Lemma free_rel_WF : ltac2:(tb__ "0|0|
S23S0S9S6S1aS0A2A1S23S36S22R4A1A1S2aR5R4R3R2A4S36S22R3A1A1F_;F_;FA';Ftr;Fb;FA;").
Proof.
  intros A b tr A' HW [(_ & -> & _) | (p & n & Hin & _ & Hy & _)]; [exact HW|].
  exact (free_wf _ _ _ _ _ HW Hin Hy).
Qed.

Definition minv_frame_stmt (C : mconsts) : Prop := ltac2:(tb__ "0|f|
S23S56Q40M0A1M1SaS56Q8A1A1M2F_;G1S7F_;S5aG1G2Fx;G1S7Fx;S5aS27VC;R7R6R5R4A5S0S1S31Z0R1A2S32R1S34Z2Z40A2A2A2S3S28VC;RaR2A3S3S1S31S4eVC;A1M3R2A2S32R2S33G3Z38A2A2A2S3S1S31S50VC;A1M4R2A2S32R2S33G4Z4M5A2A2A2S3S1S31S51VC;A1M6R2A2S32R2S33G6Z60A2A2A2S3S1S31S52VC;A1M7R2A2S32R2S33G7Z1bA2A2A2S3S1S31S4fVC;A1M8R2A2S32R2S33G8G5A2A2A2S3S1S31S4dVC;A1M9R2A2S32R2S33G9Z20A2A2A2S3S1S31S4cVC;A1MaR2A2S32R2S33GaZ8MbA2A2A2S1S31S4bVC;A1McR2A2S32R2S33GcGbA2A2A2A2A2A2A2A2A2A2A2S1S2G2R7S57G0R3A2MdA1RaGdA1A3S2S7R6GdA1R9GdA1A3A2F_;F_;Fa;S2S9S6G1G1A2A1MeS5dR3A1S5dR6A1A3S2GeS5eR4A1S5eR7A1A3S2G1S5bR5A1S5bR8A1A3S2G1S60R6A1S60R9A1A3S2GeS5fR7A1S5fRaA1A3S2G1S5cR8A1S5cRbA1A3S2S7S1eS22RfA1A1SeA3S27VC;R10RcRbRaA5F_;F_;F_;F_;F_;F_;F_;F_;F_;Fvm';Fwok';Frd';Fvm;Fwok;Frd;FA;").

Definition minv_blocks_stmt (C : mconsts) : Prop := ltac2:(tb__ "0|9|
S23S56Q40M0A1M1SaS56Q8A1M2A1M3F_;G1S7F_;S5aS0S0S27VC;R6R5R4R3A5S58S6S0S0A2M4S8S0S0R3R2A4M5S24R7A1A3S1S2S0S35R4Z10A2Z0M6A3S1S32G6R4A2S1S32S33R4R3A2M7S34Z2Z3fA2A2S1S0S1S31R5R1A2S32R1S33R5R4A2A2A2S1S2S7R8S57G0R2A2M8A1SeA3S1S5S2G3R9G8A1S14G2A1A3A1S5S28VC;RaR2A3A1A2A2F_;Fa;S0S0S58G4S8S0S0R2R1A4S24RaA1A3S5S2G4G5S8S0S0R7R6A4A3A1S3S31S33R8R7A2R4A2S31G7R8A2A2F_;F_;Fn';Fb';A2A2A2A2F_;F_;Fn;Fb;Fvm;Fwok;Frd;FA;").

Definition minv_client_write_stmt (C : mconsts) : Prop := ltac2:(tb__ "0|4|
S23S56Q40M0A1M1SaS56Q8A1M2A1M3F_;G1S7F_;S5aS0G2S27VC;R6R5R4R3A5S1S31Z0R3A2S32R3S34Z2Z40A2A2A2S5S28VC;R8R4A3A1S4S0S0S4S0S0S1S58S6S0S0A2S8S0S0R2R1A4S24RbA1A3S1S31R2R7A2S32R7S33R2R1A2A2A2A2Ln;A2Lb;A2S27VC;RaG1S7G3L_;S63G0R1S57G0R7A2A3SfG2R6A2RaR1A1X7x2Lx;R8R7A5F_;F_;F_;F_;Fv;Fa;Fvm;Fwok;Frd;FA;").
