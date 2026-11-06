(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.boost_beast.http_request.lib.Common Require KReplay.
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.boost_beast.http_request.lib Require Import HeapCeil.
From OSSVerify.Proofs.boost_beast.http_request.lib.Lib Require Import Tac Image ZBridge SysStep SFModel CellsX Arr Frame TacX.
From OSSVerify.Proofs.boost_beast.http_request.lib.As Require Import ASegs AsShadow AsConst AsIface AsCXXHeap AsWalk AsStack0.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition P_A_BP_PARSE_TOKEN_TO_EOL : Z := 0xd287c.   (* [comment removed for export] *)
Definition P_A_EC_CTOR_HTTP         : Z := 0xb8c60.   (* [comment removed for export] *)
Definition P_A_SV_COPY              : Z := 0xb852c.   (* [comment removed for export] *)
Definition P_A_FS_MALLOC_0          : Z := 0x5a438.   (* [comment removed for export] *)
Definition P_A_ECAT_FAILED          : Z := 0xa5508.   (* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition ARVT_HTTP_ECAT : Z := 0x1165a8.   (* [comment removed for export] *)
Definition AVP_HTTP_ECAT  : Z := 0x1165b8.   (* [comment removed for export] *)
Definition AVS_HTTP_ECAT_0  : Z := 0xb9100.  Definition AVS_HTTP_ECAT_8  : Z := 0xb910c.  Definition AVS_HTTP_ECAT_16 : Z := 0xb9124.
Definition AVS_HTTP_ECAT_24 : Z := 0xb91ac.  Definition AVS_HTTP_ECAT_32 : Z := 0xb92d4.  Definition AVS_HTTP_ECAT_40 : Z := 0xb9354.
Definition AVS_HTTP_ECAT_48 : Z := 0xa5508.
Definition AG_HTTP_CAT       : Z := 0x65bb90.   (* [comment removed for export] *)
Definition AG_HTTP_CAT_GUARD : Z := 0x65bbc8.   (* [comment removed for export] *)
Definition AL_HTTP_CAT_ID        : Z := 0x10450.   (* [comment removed for export] *)
Definition AL_CAT_ID_SYSGEN_SHR1 : Z := 0x10318.   (* [comment removed for export] *)
Definition HTTP_CAT_ID : Z := 0x964627da815bf210.
(* [comment removed for export] *)
Definition ALOC_TTE_NM : Z := 0x117b00.  Definition ALOC_TTE_NM2 : Z := 0x117b18.  Definition ALOC_TTE_BADLE : Z := 0x117b30.
(* [comment removed for export] *)
Definition HE_NEED_MORE := 3.  Definition HE_BAD_LINE_ENDING := 11.

(* [comment removed for export] *)
(* [comment removed for export] *)
Record ecv := mkEC { ec_val : Z ; ec_cat : Z ; ec_flags : Z }.
Definition EC_clear : ecv := mkEC 0 0 0.
Definition ec_make (e cat : Z) : ecv := mkEC e cat (if e =? 0 then 2 else 3).
Definition ec_make_loc (e cat loc : Z) : ecv := mkEC e cat (loc + (if e =? 0 then 0 else 1)).
Definition ec_failed (E : ecv) : bool := Z.odd (ec_flags E).
Definition ec_ok (E : ecv) : Prop :=
  0 <= ec_val E < 2^32 /\ 0 <= ec_cat E < 2^64 /\ 0 <= ec_flags E < 2^64 /\ ec_flags E <> 1.
Definition ErrCodeCells (E : ecv) : list cell := [C8 (wz (ec_val E)); C8 (wz (ec_cat E)); C8 (wz (ec_flags E))].
Definition EC_http (e : Z) : ecv := ec_make e AG_HTTP_CAT.
Definition EC_http_loc (e loc : Z) : ecv := ec_make_loc e AG_HTTP_CAT loc.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition is_ctl (c : Z) : bool := ((c <? 32) && negb (c =? 9)) || (c =? 127).
Definition zb (b : byte) : Z := bv_unsigned b.
Definition zbytes (bs : list byte) : list Z := map zb bs.
Fixpoint find_ix (f : Z -> bool) (bs : list byte) : option nat :=
  match bs with
  | [] => None
  | b :: bs' => if f (zb b) then Some 0%nat else option_map S (find_ix f bs')
  end.
Lemma find_ix_Some : forall f bs i, find_ix f bs = Some i ->
  (i < length bs)%nat /\ (exists b, nth_error bs i = Some b /\ f (zb b) = true)
  /\ (forall j b, (j < i)%nat -> nth_error bs j = Some b -> f (zb b) = false).
Proof.
  intros f bs. induction bs as [|b bs IH]; intros i H; cbn in H; [discriminate|].
  destruct (f (zb b)) eqn:Fb.
  - inversion H; subst. cbn. split; [lia|]. split; [exists b; split; [reflexivity|exact Fb]|].
    intros j b' Hj. lia.
  - destruct (find_ix f bs) as [i'|] eqn:E; cbn in H; [|discriminate]. inversion H; subst.
    destruct (IH i' eq_refl) as (L & (b1 & N1 & F1) & R). cbn. split; [lia|]. split; [exists b1; split; assumption|].
    intros j b' Hj N. destruct j as [|j]; cbn in N. { inversion N; subst. exact Fb. } apply (R j b'); [lia| exact N].
Qed.
Lemma find_ix_None : forall f bs, find_ix f bs = None -> forall j b, nth_error bs j = Some b -> f (zb b) = false.
Proof.
  intros f bs. induction bs as [|b bs IH]; intros H j b' N; [destruct j; discriminate|].
  cbn in H. destruct (f (zb b)) eqn:Fb; [discriminate|].
  destruct (find_ix f bs) eqn:E; [discriminate|].
  destruct j as [|j]; cbn in N. { inversion N; subst; exact Fb. } exact (IH eq_refl j b' N).
Qed.
Lemma find_ix_first : forall f bs j b,
  (forall j' b', (j' < j)%nat -> nth_error bs j' = Some b' -> f (zb b') = false) ->
  nth_error bs j = Some b -> f (zb b) = true -> find_ix f bs = Some j.
Proof.
  intros f bs. induction bs as [|x bs IH]; intros j b PREV N Fb; [destruct j; discriminate|].
  destruct j as [|j]; cbn in N.
  - inversion N; subst. cbn. rewrite Fb. reflexivity.
  - cbn. rewrite (PREV 0%nat x) by (try lia; reflexivity).
    rewrite (IH j b); [reflexivity| | exact N | exact Fb].
    intros j' b' Hj' N'. apply (PREV (S j') b'); [lia| exact N'].
Qed.
Lemma find_ix_all : forall f bs,
  (forall j b, nth_error bs j = Some b -> f (zb b) = false) -> find_ix f bs = None.
Proof.
  intros f bs. induction bs as [|x bs IH]; intros ALL; [reflexivity|]. cbn.
  rewrite (ALL 0%nat x eq_refl). rewrite IH; [reflexivity|]. intros j b N. exact (ALL (S j) b N).
Qed.
Lemma zb_range : forall b, 0 <= zb b < 256.
Proof. intros b. unfold zb. pose proof (bv_unsigned_in_range 8 b) as H. unfold bv_modulus in H. cbn in H. lia. Qed.
Lemma is_ctl_spec : forall c, 0 <= c < 256 -> is_ctl c = true <-> (c < 32 /\ c <> 9) \/ c = 127.
Proof.
  ltac2:(KReplay.run [|constr:(@Corelib.Numbers.BinNums.Z); constr:(@Corelib.Init.Logic.and); constr:(@Stdlib.ZArith.BinInt.Z.le); constr:(@Corelib.Numbers.BinNums.Z0); constr:(@Stdlib.ZArith.BinInt.Z.lt); constr:(@Corelib.Numbers.BinNums.Zpos); constr:(@Corelib.Numbers.BinNums.xO); constr:(@Corelib.Numbers.BinNums.xH); constr:(@Corelib.Init.Logic.iff); constr:(@Corelib.Init.Logic.eq); constr:(@Corelib.Init.Datatypes.bool); constr:(@Corelib.Init.Datatypes.orb); constr:(@Corelib.Init.Datatypes.andb); constr:(@Stdlib.ZArith.BinInt.Z.ltb); constr:(@Corelib.Init.Datatypes.negb); constr:(@Stdlib.ZArith.BinInt.Z.eqb); constr:(@Corelib.Numbers.BinNums.xI); constr:(@Corelib.Init.Datatypes.true); constr:(@Corelib.Init.Logic.or); constr:(@Corelib.Classes.Morphisms.trans_co_eq_inv_impl_morphism); constr:(@Corelib.Classes.RelationClasses.iff_Transitive); constr:(@Corelib.Init.Logic.not); constr:(@Corelib.Classes.Morphisms.eq_proper_proxy); constr:(@Stdlib.Bool.Bool.orb_true_iff); constr:(@Corelib.Classes.Morphisms_Prop.or_iff_morphism); constr:(@Corelib.Classes.Morphisms.reflexive_proper_proxy); constr:(@Corelib.Classes.Morphisms.reflexive_reflexive_proxy); constr:(@Corelib.Classes.RelationClasses.iff_Reflexive); constr:(@Stdlib.Bool.Bool.andb_true_iff); constr:(@Corelib.Init.Datatypes.false); constr:(@Corelib.Classes.Morphisms.Reflexive_partial_app_morphism); constr:(@Corelib.Classes.Morphisms.respectful); constr:(@Corelib.Classes.Morphisms_Prop.and_iff_morphism); constr:(@Stdlib.Bool.Bool.negb_true_iff); constr:(@Stdlib.ZArith.BinInt.Z.ltb_lt); constr:(@Stdlib.ZArith.BinInt.Z.eqb_eq); constr:(@Stdlib.ZArith.BinInt.Z.eqb_neq); constr:(@Corelib.Init.Datatypes.cons); constr:(@Stdlib.micromega.ZMicromega.ZArithProof); constr:(@Stdlib.micromega.ZMicromega.RatProof); constr:(@Stdlib.micromega.RingMicromega.PsatzAdd); constr:(@Stdlib.micromega.RingMicromega.PsatzIn); constr:(@Corelib.Init.Datatypes.S); constr:(@Corelib.Init.Datatypes.O); constr:(@Stdlib.micromega.RingMicromega.PsatzMulC); constr:(@Stdlib.micromega.EnvRing.Pc); constr:(@Corelib.Numbers.BinNums.Zneg); constr:(@Stdlib.micromega.ZMicromega.DoneProof); constr:(@Corelib.Init.Datatypes.nil); constr:(@Corelib.Init.Datatypes.list); constr:(@Stdlib.micromega.VarMap.Elt); constr:(@Stdlib.micromega.VarMap.t); constr:(@Stdlib.micromega.Tauto.IFF); constr:(@Stdlib.micromega.RingMicromega.Formula); constr:(@Stdlib.micromega.Tauto.eKind); constr:(@Corelib.Init.Datatypes.unit); constr:(@Stdlib.micromega.Tauto.isProp); constr:(@Stdlib.micromega.Tauto.OR); constr:(@Stdlib.micromega.Tauto.AND); constr:(@Stdlib.micromega.Tauto.A); constr:(@Stdlib.micromega.RingMicromega.Build_Formula); constr:(@Stdlib.micromega.EnvRing.PEX); constr:(@Stdlib.micromega.RingMicromega.OpLt); constr:(@Stdlib.micromega.EnvRing.PEc); constr:(@Corelib.Init.Datatypes.tt); constr:(@Stdlib.micromega.Tauto.NOT); constr:(@Stdlib.micromega.RingMicromega.OpEq); constr:(@Stdlib.micromega.Tauto.BFormula); constr:(@Stdlib.micromega.ZMicromega.ZTautoChecker_sound); constr:(@Corelib.Init.Logic.eq_refl); constr:(@Stdlib.micromega.ZMicromega.ZTautoChecker); constr:(@Stdlib.micromega.VarMap.find); constr:(@Corelib.Init.Logic.False); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AXRep.is_ctl)|] [|@lemma; @B; @__ff; @__varmap; @__wit; @__x1; @__arith; @Hc; @c|] "#%(#&#q#)#&#1#3###O#`#:#$#%#a#_#=#0#*#I#X#i#,#6#7#5#4#>#F#;#A#S#T#U#k#+#?#@#C#D#E#H#J#K#L#M#W#V#Y#Z#[#\#^#f#g#j#c#b#]#l#n#o#p#m#q#r#2#N#/#9#<#B#.#-#8#G#R#Q#P#h#e#d7#a&#b&#<%#c$#1%#%%#d$#e,#f'#g$#h%#i%#=)#j.#k%#l&#m%#n%#o'#p*VS2S%G&P&#&#&#&#&#&#&#,#-G#'-#,)VS&K#).,#.K#US'#VS('#)P)#)#)#)#)#,#.K#VS)+##F#J#F-J#F&J%$#(&#VS&L7.L5US'#VS(%#.L.VS)$##F#J#F&J#F&J%$#-LA#CL?US*#'%##CL8%$#VS3D#*DEO-*G$$#j#$5#VS4s#$<#Fs#*J#Fs#'J'$#(=##F:J#F9J'$#%#5WS5DES6+DE#7/9&G88#*DEO8&#221j#$+#VS7s#7s#3#Fs#5S+(0##Fs#%S+'/#%#@k#%DDXS8DDEE+DE/30D%E$QR4#3(G/3(#s#%s#%0*DEO3(#??>j#$,#US9s#A-Ks#F(>#'s#)/%#s#,+DE91ZR>s#,G22#/2&#s#/s#/:*DEO2&#s#)s#)s#(j#$)#VS:Ks#O#CKs#C(s#?#%,s#/+DEB-0D8E7S,S-.#s#7s#1G*DEO.%#s#1s#1s#0j#$'#VS;Ks#J#CKs#UUS*#(s###+DEs#*s#<0D@E?QRs#=#s##s#;G+DEs#,s#:/8s#<$s#;s#;#*DEO/s#;#s#;s#;s#:j#$(#VS<Ks#^US.S/US.#1C#US=PVS>C#1C'WS0C$#2C'#3#S#WS0C')1CS/2C$#3#S#2C&*3#S#US?H$H&#$H'#$H&#$H)#$H.#$H/#$H,#$H-#$H,#$H/#$H4#$H5#US@HVSACKUSBCUSCCVSDCP4Cs$'5C$SE#6&NIIM#S$4Cs$'5C'S1#6)NIIM#S$ZSF*NIIM#[SG+NIIM'#4Cs#~5C,S1#6.NIIM#S$[SH/NIIM&#[SI0NIIM##VSJ1MVSKFJVSLGL#F#Jm$%#WSMCS%KXSNGL$#l#&*)#l#';:#l#(>=#j#)C#-Gs$?#CGs$=k###SO'%##CGs$6%$#(##k#)C#UGLl#*,$#Vs#Gs#F#Vs#Rs#Q#Vs#[s#Z#Vs#fs#e#Vs#ts#s#Vs$'s$&#USPK#F#J's#is#V%#s#`(%#m#(#j#+s$V#j#,C##"). Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Section HCW.
  Context {HCEIL : HeapCeil}.

Definition wcells (zs : list Z) : list cell := map (fun z => C8 (wz z)) zs.
Definition zeros (n : nat) : list byte := repeat (b8 0) n.
Definition le8z (z : Z) : list byte := le8 (wz z).

(* [comment removed for export] *)
Definition AXStatics (m : mem) : Prop :=
  rw_cells asegs m AVP_HTTP_ECAT (wcells [AVS_HTTP_ECAT_0; AVS_HTTP_ECAT_8; AVS_HTTP_ECAT_16; AVS_HTTP_ECAT_24; AVS_HTTP_ECAT_32; AVS_HTTP_ECAT_40; AVS_HTTP_ECAT_48]).

(* [comment removed for export] *)
Lemma AXStatics_transport : forall W m m',
  AXStatics m -> munch W m m' -> wmono asegs m m' ->
  Forall (fun iv : Z * Z => 0x125e40 <= fst iv \/ snd iv <= 0x115000) W ->
  AXStatics m'.
Proof.
  intros W m m' XS MU WM FW.
  assert (D : forall A n, 0x115000 <= A /\ A + n <= 0x125e40 -> disjoint_from W A n).
  { intros A n HA. clear XS MU WM. induction W as [|[lo hi] W IH]; [exact I|].
    pose proof (Forall_inv FW) as H1. cbn in H1. cbn. split; [lia|]. apply IH. exact (Forall_inv_tail FW). }
  unfold AXStatics in *.
  eapply rw_cells_transport; [exact XS | exact MU | exact WM | apply D; unfold AVP_HTTP_ECAT; cbn; lia].
Qed.

(* [comment removed for export] *)
Definition AXStatics_img_ok : bool :=
  forallb (fun ac : Z * list Z =>
             match image_bytes asegs (fst ac) (8 * length (snd ac))%nat with
             | Some bs => if list_eq_dec (fun a b : byte => @base.decide (a = b) (bv_eq_dec 8 a b)) bs (flat_map le8z (snd ac)) then true else false
             | None => false end)
    [(AVP_HTTP_ECAT, [AVS_HTTP_ECAT_0; AVS_HTTP_ECAT_8; AVS_HTTP_ECAT_16; AVS_HTTP_ECAT_24; AVS_HTTP_ECAT_32; AVS_HTTP_ECAT_40; AVS_HTTP_ECAT_48]);
     (AL_HTTP_CAT_ID, [HTTP_CAT_ID]); (AL_CAT_ID_SYSGEN_SHR1, [0x595588bd12bf6fe8])].
Lemma AXStatics_img_ok_true : AXStatics_img_ok = true.
Proof. ltac2:(KReplay.run [|constr:(@Corelib.Init.Logic.eq_refl); constr:(@Corelib.Init.Datatypes.bool); constr:(@Corelib.Init.Datatypes.true); constr:(@Corelib.Init.Logic.eq); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AXRep.HCW.AXStatics_img_ok)|] Array.empty "##&###(#'#(#&#)#*#VECDWFCGDm$$##"). Qed.

(* [comment removed for export] *)
Definition AHttpCatCells (built : bool) : list cell :=
  if built then [C8 (wz AVP_HTTP_ECAT); C8 (wz HTTP_CAT_ID); CB 40 (zeros 40)] else [CB 56 (zeros 56)].
Definition AHttpCatGuardCells (built : bool) : list cell :=
  if built then [CB 8 (b8 1 :: b8 1 :: zeros 6)] else [CB 8 (zeros 8)].
Definition AHttpCat (m : mem) (built : bool) : Prop :=
  rw_cells asegs m AG_HTTP_CAT (AHttpCatCells built) /\ rw_cells asegs m AG_HTTP_CAT_GUARD (AHttpCatGuardCells built).

Lemma AHttpCat_transport : forall W m m' b,
  AHttpCat m b -> munch W m m' -> wmono asegs m m' ->
  disjoint_from W AG_HTTP_CAT 56 -> disjoint_from W AG_HTTP_CAT_GUARD 8 -> AHttpCat m' b.
Proof.
  intros W m m' b (C1 & C2) MU WM D1 D2. unfold AHttpCat.
  destruct b; (split; [ eapply rw_cells_transport; [exact C1 | exact MU | exact WM | exact D1]
                     | eapply rw_cells_transport; [exact C2 | exact MU | exact WM | exact D2] ]).
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition AASSIGN_STACK : Z := 48 + AINTRIN_STACK.

Definition aassign_W (D lo : Z) (sp : word) : list (Z * Z) :=
  [(lo, bv_unsigned sp); (D, D + 24); (AG_HTTP_CAT, AG_HTTP_CAT + 64)]%Z.

Definition aassign_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (D e lo shi : Z) (retD : bool) (m : mem) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom asegs)
    /\ munch (aassign_W D lo sp) m m' /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ stk asegs m' lo (bv_unsigned sp)
    /\ rw_cells asegs m' D (ErrCodeCells (EC_http e))
    /\ AHttpCat m' true /\ AXStatics m'
    /\ ACONST m' /\ stack0 m' lo shi                                   (* [comment removed for export] *)
    /\ (retD = true -> a0 = Z_to_bv 64 D).

Definition aassign_stmt (pc_entry : Z) (retD : bool) : Prop :=
  forall ra sp gp tp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : mem) (D e lo shi : Z) (g : bool) (junk : list byte),
  rw_cells asegs m D [CB 24 junk] ->
  AHttpCat m g -> AXStatics m ->
  stk asegs m lo (bv_unsigned sp) -> lo + AASSIGN_STACK <= bv_unsigned sp -> aceil <= lo ->   (* [comment removed for export] *)
  bv_unsigned sp <= D -> D + 88 <= shi -> D mod 8 = 0 ->                                      (* [comment removed for export] *)
  1 <= e < 2^31 ->
  mem_inv asegs m ->
  ACONST m -> stack0 m lo shi -> bv_unsigned sp + 64 <= shi ->                                  (* [comment removed for export] *)
  evt asegs (aassign_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc D e lo shi retD m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 D) (Z_to_bv 64 e) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 pc_entry) fc None m (seg_rom asegs)).

(* [comment removed for export] *)
Definition aassignA_stmt : Prop := aassign_stmt P_A_EC_CTOR_HTTP false.

(* [comment removed for export] *)

End HCW.
