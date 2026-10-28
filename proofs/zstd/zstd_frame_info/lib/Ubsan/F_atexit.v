(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout State Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.zstd.zstd_frame_info.lib.Lib Require Import Tac Arr Bytes ITree Nodes Decode SysStep RegsEquiv.
From OssFuzzTheorems.Proofs.zstd.zstd_frame_info.lib.Common Require Import StrFun STRW_tac Startup_kit DrvAgree.
From OssFuzzTheorems.Proofs.zstd.zstd_frame_info.lib.Ubsan Require Import UImg.
Import ListNotations.
Open Scope bv_scope.
Import ITree.Exc.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition PATEXIT : Z := 0x1405c.        (* [comment removed for export] *)
Definition PATX : Z := 0x4e070.           (* [comment removed for export] *)
Definition PATX_CALLFN : Z := 0x14120.    (* [comment removed for export] *)
Definition PNEED_LOCKS : Z := 0x4e2bb.    (* [comment removed for export] *)
Definition PATEXIT_STACK : Z := 48.
(* [comment removed for export] *)
Definition PEXIT_GUARD : Z := 0x12c14.    (* [comment removed for export] *)
Definition PAEF_INCB : Z := 0x2df34.      (* [comment removed for export] *)

(* [comment removed for export] *)
Definition atx_cells (head slot f0 a0 : Z) (m : word -> option byte) : Prop :=
  rw_cells usegs m 0x4e070 [C1 (Z_to_bv 8 0)]
  /\ rw_cells usegs m (0x4e074) [C4 (Z_to_bv 64 0)]
  /\ rw_cells usegs m (0x4e078) [C4 (Z_to_bv 64 slot)]
  /\ rw_cells usegs m (0x4e080) [C8 (Z_to_bv 64 head)]
  /\ rw_cells usegs m (0x4e088) [C8 (Z_to_bv 64 0)]
  /\ rw_cells usegs m (0x4e090) [C8 (Z_to_bv 64 f0)]
  /\ rw_cells usegs m (0x4e190) [C8 (Z_to_bv 64 a0)].

(* [comment removed for export] *)
Definition atx_state (reg : bool) (m : word -> option byte) : Prop :=
  atx_cells (if reg then 0x4e088 else 0) (if reg then 1 else 0) (if reg then PATX_CALLFN else 0) (if reg then PEXIT_GUARD else 0) m
  /\ rw_cells usegs m PAEF_INCB [C1 (Z_to_bv 8 0)].

(* [comment removed for export] *)
Definition atx_addr (a : Z) : Prop :=
  (0x4e070 <= a < 0x4e071)%Z \/ (0x4e074 <= a < 0x4e07c)%Z \/ (0x4e080 <= a < 0x4e098)%Z \/ (0x4e190 <= a < 0x4e198)%Z.

Definition atx_state_addr (a : Z) : Prop := atx_addr a \/ (PAEF_INCB <= a < PAEF_INCB + 1)%Z.

Lemma atx_cells_agree : forall (P : Z -> Prop) m m' head slot f0 a0,
  magree usegs P m m' -> (forall a, atx_addr a -> P a) -> atx_cells head slot f0 a0 m -> atx_cells head slot f0 a0 m'.
Proof.
  intros P m m' head slot f0 a0 AG HP (A1 & A2 & A3 & A4 & A5 & A6 & A7). unfold atx_cells.
  Ltac agx AG HP A := eapply rw_cells_magree; [exact AG| exact A| intros a Ha; apply HP; unfold atx_addr, PATX in *; cbn in Ha; lia].
  Local Ltac2 Set LiaHints.tbl := fun () => "0010>42299608260.18000004S2Ha".
split; [agx AG HP A1|]. split; [agx AG HP A2|]. split; [agx AG HP A3|]. split; [agx AG HP A4|].
  split; [agx AG HP A5|]. split; [agx AG HP A6| agx AG HP A7].
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".

Lemma atx_state_agree : forall (P : Z -> Prop) m m' reg,
  magree usegs P m m' -> (forall a, atx_state_addr a -> P a) -> atx_state reg m -> atx_state reg m'.
Proof.
  intros P m m' reg AG HP [AX CB]. split.
  - eapply atx_cells_agree; [exact AG| intros a Ha; apply HP; left; exact Ha| exact AX].
  - Local Ltac2 Set LiaHints.tbl := fun () => "0010=2687138761.10000004S2Ha".
eapply rw_cells_magree; [exact AG| exact CB| intros a Ha; apply HP; right; unfold PAEF_INCB in *; cbn in Ha; lia].
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".

Lemma atx_state_munch : forall W m m' reg,
  munch W m m' -> wmono usegs m m' -> (forall a, atx_state_addr a -> outside W a) -> atx_state reg m -> atx_state reg m'.
Proof. intros W m m' reg MU WM HW. apply (atx_state_agree _ _ _ _ (magree_of_munch _ _ _ _ MU WM)). intros a Ha. cbn. apply HW. exact Ha. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition patexit_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (lo g : Z) (m : word -> option byte) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 0) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom usegs)
    /\ munch [(bv_unsigned sp - 48, bv_unsigned sp); (0x4e078, 0x4e07c); (0x4e080, 0x4e088); (0x4e090, 0x4e098); (0x4e190, 0x4e198)]%Z m m'
    /\ wmono usegs m m' /\ mem_inv usegs m'
    /\ stk usegs m' lo (bv_unsigned sp)
    /\ atx_cells (0x4e088) 1 PATX_CALLFN g m'.

Lemma patexit_spec : forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (lo g : Z),
  stk usegs m lo (bv_unsigned sp) ->
  atx_cells 0 0 0 0 m ->
  rw_cells usegs m PNEED_LOCKS [C1 (Z_to_bv 8 0)] ->
  mem_inv usegs m ->
  a0 = Z_to_bv 64 g -> (0 <= g < 2^64)%Z ->
  (lo <= bv_unsigned sp - 48)%Z -> (0x4f000 <= lo)%Z ->
  evt usegs (patexit_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo g m)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 PATEXIT) fc None m (seg_rom usegs)).
Proof.
  intros until g. intros ST (X1 & X2 & X3 & X4 & X5 & X6 & X7) NL MI -> Hg LO LOLO.
  unfold PATX, PNEED_LOCKS, PATEXIT in *.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
  pose proof (munch_refl [(bv_unsigned sp - 48, bv_unsigned sp); (0x4e078, 0x4e07c); (0x4e080, 0x4e088); (0x4e090, 0x4e098); (0x4e190, 0x4e198)]%Z m) as MU.
  pose proof (wmono_refl usegs m) as WM.
  Local Ltac2 Set LiaHints.tbl := fun () => "01b0>10873507702.6011462967374.6011903774446.6312299880250.6215315362126.631800609155.62 19693786893.6620109792462.6220393288378.6521256664762.6722389541692.6024638473347.6224638473347.6326235044154.6227865992944.6627906909861.5427908601838.6028178678458.6728331348917.6728417259964.6230873494640.6231378308326.5333680001082.6334004991342.6234430152252.6334629141429.6535310472686.6236066158.62   36370459630.6237319879630.6237351378874.6637370272442.6537467297293.6737558276410.6238889585390.6339024948917.6639661655098.6239693769198.603976114874.65 40069102958.6240457739452.6240959947248.6541412757005.6541710833594.6641930314042.6242102643258.6642387372858.6542744733806.6243059266230.5143185646906.624334394958.62 43913974254.6243988483203.6043988483203.6144338668016.6744500894574.6244605926074.6745221239098.6245367810746.6745848756903.6046468661564.6247472103150.6349147187950.6349649769127.6349676673978.6649978085870.625039673326.60 50837928942.6051711223320.5352105090727.6252320852277.6252567164907.6052567164907.6252567164907.6352567164907.6552567164907.6652567164907.6752620110522.6553078870714.6753850141114.6653961827318.6054243526019.6254569212142.63563227834.62  56912526318.6057597764590.6257745675194.6257774688366.6358732652910.6259377599629.6259382628974.6260128159214.6260258122606.626034025274.67 60592618094.6260858483367.6261353657710.606152788666.65 61559103930.666269928558.62 63305555623.6264997134979.636593737402.67 67168240058.6267663283182.6268180518586.6568578752238.628384152046.60 8583720762.60 8722841838.63 9256566202.66 9595551854.62 9844715886.62 992066670.62  00000100:00C00D00M00N00O00X00Y00Z00^00_00`00a00b00f00o01001901=01>01?01D01M01Q01Z01c01l02502>02?02@02A02B02K02T02U02^02_02h02l02m02n02o03003103203;03?03@03I03R03S03T03U03^03_03d03e03f03j04304<04=04>04G04P04Y04Z04[04d04e04f04g04h04i04j04k04l04m04n04o05805=05F05O05T05]05f05g06006906B06C06L06M06V06W06X06a06b06c06d06e06n06o07807A07F07O07P07Y07b07kSS2LO4LOLOS2LO4LOLOSS2LO4LOLOSSS2LO4LOLOSSS2HBSSSSS2LOS2LO4LOLOSS2LO4LOLOS2HBSSS3RSPS2LO4LOLOS2HBS2LO4LOLOS2LO4LOLOS2LO4LOLOS2LO4LOLOS2LO4LOLOSSSSS2LO4LOLOS2LO4LOLOSS2LO4LOLOSS2LO4LOLOS2HBSSSSSSS2LO4LOLOS2LOSS2LO4LOLOS2LO4LOLOSSSS2LO4LOLOSS3RSPSSS2HBS2LO4LOLOS2LO4LOLOSSS2LO4LOLOS2LO4LOLOS2LO4LOLOSSS2LO4LOLOSSSSSSSSSSSS2LO4LOLOS3RSPS2LO4LOLOS2LO4LOLOS3RSPS2LO4LOLOS2LO4LOLOSS2LO4LOLOS2LO4LOLOS2LO4LOLOSS2LO4LOLOSS2LO4LOLOSSS2LO4LOLOSSSSS2LO4LOLOSS2LO4LOLOS2LO4LOLOS3RSPS2LO4LOLOSS2LO4LOLOS2LO4LOLOS2LO4LOLO".
carve_frame 48%nat ST.
  (* [comment removed for export] *)
  steps_to 0x1b848%Z.
  (* [comment removed for export] *)
  lstep. lstep. lstep. change (sxb (Z_to_bv 8 0)) with (Z_to_bv 64 0 : word). if_true. lstep.
  steps_to 0x1408c%Z.
  (* [comment removed for export] *)
  lstep. lstep. lstep. if_false.
  (* [comment removed for export] *)
  lstep. lstep. if_false. lstep. lstep.
  (* [comment removed for export] *)
  lstep. try replace (sx32 (Z_to_bv 64 0)) with (Z_to_bv 64 0 : word) by (vm_compute; reflexivity).
  lstep. lstep. if_true.
  (* [comment removed for export] *)
  steps_to 0x1bad0%Z.
  (* [comment removed for export] *)
  lstep. try replace (sx32 (Z_to_bv 64 0)) with (Z_to_bv 64 0 : word) by (vm_compute; reflexivity).
  lstep. if_false. lstep.
  (* [comment removed for export] *)
  steps_to 0x14118%Z.
  release_frame FR ST (bv_unsigned sp). astep. astep.
  unfold patexit_post, atx_cells, PATX, PATX_CALLFN. sys_finish.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
