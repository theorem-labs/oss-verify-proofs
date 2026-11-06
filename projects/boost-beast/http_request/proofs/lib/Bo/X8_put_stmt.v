(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.boost_beast.http_request.lib.Common Require KReplay.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.boost_beast.http_request.lib.As Require TP_0Gc. (* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.boost_beast.http_request.lib Require Import HeapCeil.
From OSSVerify.Proofs.boost_beast.http_request.lib.Lib Require Import Tac Image ZBridge SysStep SFModel CellsX Arr TacX Exec.
From OSSVerify.Proofs.boost_beast.http_request.lib.Bo Require Import BSegs AsShadow AsConst AsIface AsIface5 AsCXXHeap AsWalk AsStack0 AXPres AXKit AXRep AXRep2 AXPRep AXPRep2 AXRep_fields AXRep_mbuf AXImgKit X8Kit X8SRKit X8_P_ftab_rep X8_F_insert2 X8_F_insert4 X8_state1_stmt X8_state2_stmt X8_mbuf_stmt X8_pst.
From OSSVerify.Proofs.boost_beast.http_request.lib.RB Require Import RBMem RBShape DList.
From OSSVerify.Proofs.boost_beast.http_request.lib.Spec Require Import Prelim.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition BPUT_STACK : Z := 304 + (64 + OCB_STACK).   (* [comment removed for export] *)

Lemma BPUT_STACK_val : BPUT_STACK = 9520.               (* [comment removed for export] *)
Proof. reflexivity. Qed.

(* [comment removed for export] *)
Definition PARSER_SIZE : Z := 344.

(* [comment removed for export] *)
Definition put_X (P E : Z) (L0 : list Z) (es0 : list mbe) : list (Z * Z) :=
  (P, P + 242) :: (E, E + 24) :: (AG_HTTP_CAT, AG_HTTP_CAT + 64) :: (AG_FIELD_TABLE, AG_FIELD_TABLE + 3456) :: elemsW L0 ++ mb_elemsW es0.

(* [comment removed for export] *)
Definition elems_off (em : gmap Z elt) (A n : Z) : Prop := forall e d, em !! e = Some d -> A + n <= e \/ e + esize d <= A.
Definition body_off (es : list mbe) (A n : Z) : Prop := forall x s, In (x, s) es -> A + n <= x \/ x + mb_block_size s <= A.
Definition hdrs_off (h : hdrv) (A n : Z) : Prop :=
  (hv_tl h <> 0 -> A + n <= hv_tp h \/ hv_tp h + hv_tl h <= A) /\ (hv_ml h <> 0 -> A + n <= hv_mp h \/ hv_mp h + hv_ml h <= A).
Definition ps_off (d : pst) (A n : Z) : Prop := elems_off (ps_em d) A n /\ body_off (ps_es d) A n /\ hdrs_off (ps_h d) A n.

Section HCW.
  Context {HCEIL : HeapCeil}.
  Variable H : asr.

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition PutU (P p0 : Z) (bs : list byte) (mb : byte) (d : pst) (m : mem) : Prop :=
  AFieldsC m (P + 80) (ps_S d) (ps_L d) (ps_ns d) (ps_ls d) (ps_em d)
  /\ rw_cells bsegs m (P + O_PR_HDR) (HdrCells (ps_h d)) /\ rw_cells bsegs m (P + O_PR_USED) [C1 (b8 (ps_u d))]
  /\ AMBuf m (P + 168) (ps_es d) (ps_insz d) /\ rw_cells bsegs m (P + 232) [C8 (wz (P + 168))]
  /\ rw_cells bsegs m (P + O_PR_MERGE) [C1 mb] /\ rw_cells bsegs m (P + 288) [C8 (wz 0)] /\ rw_cells bsegs m (P + 336) [C8 (wz 0)]
  /\ bytes_at bsegs m p0 bs /\ APfTab m /\ FTInit m /\ AXStatics2 m.

(* [comment removed for export] *)
Definition PutL (sp : word) (P E p0 : Z) (bs : list byte) (LB0 : list block) (L0 : list Z) (es0 : list mbe) (h0 : hdrv) (d : pst) : Prop :=
  let LB := ps_LBn d ++ LB0 in
  pcore_ok (ps_c d)
  /\ AFieldsOwn LB (ps_em d) /\ AMBufOwn LB (ps_es d)
  /\ new_elems_off H LB0 (bv_unsigned sp) L0 (ps_L d) /\ new_body_off H LB0 (bv_unsigned sp) es0 (ps_es d)
  /\ ps_off d P PARSER_SIZE /\ ps_off d E 24 /\ ps_off d p0 (Z.of_nat (length bs))                     (* [comment removed for export] *)
  /\ (forall e, e ∈ ps_L d -> e + 48 <= p0 \/ p0 + Z.of_nat (length bs) <= e)                            (* [comment removed for export] *)
  /\ (forall e d', (ps_em d) !! e = Some d' -> forall x s, In (x, s) (ps_es d) -> e + esize d' <= x \/ x + mb_block_size s <= e)
  /\ (pc_state (ps_c d) <= 1 -> hdr_empty (ps_h d) /\ ps_u d = 0) /\ 0 <= ps_u d <= 1
  /\ mb_cap (ps_es d) <= 3 * ps_insz d + 512 /\ Z.of_nat (length (ps_es d)) <= KB /\ 0 <= ps_insz d
  /\ (pc_state (ps_c d) = 3 \/ pc_state (ps_c d) = 4 \/ pc_state (ps_c d) = 9 -> 1 <= pc_len (ps_c d))
  /\ hdr_disj (ps_L d) (ps_es d) (ps_h d)
  /\ hdr_new H LB0 (bv_unsigned sp) h0 (ps_h d)
  /\ (pc_state (ps_c d) < 10 -> pc_hlim (ps_c d) <= 8192) /\ pc_skip (ps_c d) < 2^62
  /\ lbn_ownedP (ps_L d) (ps_h d) (ps_es d) (ps_LBn d)
  /\ lsub L0 (ps_L d) /\ (forall x s, In (x, s) es0 -> In (x, s) (ps_es d))
  /\ 0 <= ps_A d.

  Variables MX CX MA MR : Z.  (* [comment removed for export] *)

(* [comment removed for export] *)
Definition PutB (LB0 : list block) (p0 R : Z) (d : pst) (p : Z) : Prop :=
  lb_bytes (ps_LBn d ++ LB0) + 17 * pc_hlim (ps_c d) + body_res (ps_es d) (ps_insz d) (R - (p - p0))
       + (if pc_state (ps_c d) <=? 9 then 34 else 0) <= MX
  /\ 4 * Z.of_nat (length (ps_LBn d ++ LB0)) + pc_hlim (ps_c d) + 4 * (KB - Z.of_nat (length (ps_es d)))
       + (if pc_state (ps_c d) <=? 1 then 8 else 0) + (if pc_state (ps_c d) <=? 9 then 2 else 0) <= 4 * CX
  /\ ps_insz d + (R - (p - p0)) <= 2^26
  /\ ps_A d + 17 * pc_hlim (ps_c d) + body_res (ps_es d) (ps_insz d) (R - (p - p0))
       + (if pc_state (ps_c d) <=? 9 then 34 else 0) <= MA.
Scheme kc__1 := Elimination for Corelib.Init.Datatypes.bool Sort Prop.

Lemma pot_if_range : forall st, 0 <= (if st <=? 9 then 34 else 0) <= 34 /\ 0 <= (if st <=? 9 then 2 else 0) <= 2 /\ 0 <= (if st <=? 1 then 8 else 0) <= 8.
Proof. ltac2:(KReplay.run [|constr:(@Corelib.Numbers.BinNums.Z); constr:(@Stdlib.ZArith.BinInt.Z.leb); constr:(@Corelib.Numbers.BinNums.Zpos); constr:(@Corelib.Numbers.BinNums.xI); constr:(@Corelib.Numbers.BinNums.xO); constr:(@Corelib.Numbers.BinNums.xH); constr:(@Corelib.Init.Datatypes.bool); constr:(@kc__1); constr:(@Corelib.Init.Logic.and); constr:(@Stdlib.ZArith.BinInt.Z.le); constr:(@Corelib.Numbers.BinNums.Z0); constr:(@Corelib.Init.Logic.conj); constr:(@Corelib.Init.Datatypes.nil); constr:(@Stdlib.micromega.ZMicromega.ZArithProof); constr:(@Corelib.Init.Datatypes.list); constr:(@Stdlib.micromega.VarMap.Empty); constr:(@Stdlib.micromega.VarMap.t); constr:(@Stdlib.micromega.Tauto.A); constr:(@Stdlib.micromega.RingMicromega.Formula); constr:(@Stdlib.micromega.Tauto.eKind); constr:(@Corelib.Init.Datatypes.unit); constr:(@Stdlib.micromega.Tauto.isProp); constr:(@Stdlib.micromega.RingMicromega.Build_Formula); constr:(@Stdlib.micromega.EnvRing.PEc); constr:(@Stdlib.micromega.RingMicromega.OpLe); constr:(@Corelib.Init.Datatypes.tt); constr:(@Stdlib.micromega.Tauto.BFormula); constr:(@Stdlib.micromega.ZMicromega.ZTautoChecker_sound); constr:(@Corelib.Init.Logic.eq_refl); constr:(@Corelib.Init.Datatypes.true); constr:(@Corelib.Init.Logic.eq); constr:(@Stdlib.micromega.ZMicromega.ZTautoChecker); constr:(@Stdlib.micromega.VarMap.find)|] [|@b; @__ff; @__varmap; @__wit; @__arith; @st|] "#$g#&#G#)###3#=#/#>#A#<#B#%#.#,#$#6#F#5#7#8#9#;#C#E#H#G#I#D#1#2#4#?#:#+#-#@#*#0-#=%#>%#?'#@'#A*#B$#C$#D%#E%#F')M)#UN#(#+D#)&UN#)#(#nG#$##CD#%###E$E#$$%#$#(/nG#$##CD#%###E$E#$$%#$#(M+L#(1nG#$##C$#%###E$E#$$%#$##*##0#j#$G#+O,$E7$88#$#$E5$66#$#nG#$##CD#%#1#E$E#$$3#$##'##+#j#$G#$E8$99#$##-#URPUS#PUS$CUS%CUS&C*CE*Cs#.&C$I#'&JFFH#KVS''HVS(GQVS)DLWS*G#Qm$%#WS+CEOXS,DL$#l#%*)#l#&10#l#'43#l#(#s#&Dm##s#'&C1I1'4JFFH#Kl#%#0*l#&87#l#';:#l#(#s#,Dm##s#-%s#/s#.*#m##s#.*Cs#A&C<I#'>JFFH#Kl#%#:4l#&BA#l#'s#%s#$#l#(#s#4Dm##s#5&C*I*'s#%JFFH#Kl#%#A;l#&s#)s#(#l#'s#,s#+#l#(#s#:Dm##s#;%s#=s#<*#m##s#<*Cs#K&Cs#-I#'s#/JFFH#Kl#%#s#+s#%l#&s#3s#2#l#'s#6s#5#l#(#s#;Dm##s#<&C*I*'s#6JFFH#Kl#%#s#2s#,l#&s#:s#9#l#'s#=s#<#l#(#s#ADm##s#B%s#Ds#C*#m##s#C%s#Ns#D4#m##s#D%s#Ss#Es#'##s#Ts#Fm#$#$EE##s#L#s#U#&Cs#EIs#E's#GJFFH#Kl#%#s#Cs#=l#&s#Ks#J#l#'s#Ns#M#l#(#*Dm##+%,s#U#;m##,%s#_-s#%#m##-%s#d.s#8##s#e/m#$#,s#]4#Dl#$s#kG##5s#k#6s#i##s#d#%#j#$G##&s#a%;s#q2s#Lm##)%=s#p4s#=m##*%+s#f#s#%m##(%.)'##/*m#$##0s##%1s#$):m##$%4%-##5&m#$#,3)#Dl#$s$&G#,s$(:#Dl#$s$@G#j#)C##"). Qed.

(* [comment removed for export] *)
Definition put_pure (sp : word) (P E lo shi : Z) (p0 : Z) (bs : list byte) : Prop :=
  1 <= Z.of_nat (length bs) /\ lo + BPUT_STACK <= bv_unsigned sp /\ aceil <= lo
  /\ P mod 8 = 0 /\ E mod 8 = 0
  /\ (P + PARSER_SIZE <= E \/ E + 24 <= P)
  /\ (p0 + Z.of_nat (length bs) <= P \/ P + PARSER_SIZE <= p0) /\ (p0 + Z.of_nat (length bs) <= E \/ E + 24 <= p0)
  /\ bv_unsigned sp mod 16 = 0 /\ bv_unsigned sp <= shi.

Definition put_static (sp tp : word) (P E lo B shi p0 R : Z) (bs : list byte) : Prop :=
  put_pure sp P E lo shi p0 bs
  /\ Z.of_nat (length bs) <= R
  /\ bv_unsigned sp <= B
  /\ tp = Z_to_bv 64 ATP
  /\ MX <= as_LIVE_MAX H /\ CX <= as_LIVE_CNT_MAX H.

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition bput_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (s : as_St H) (LB0 : list block) (LF : list fframe) (P E lo B shi : Z) (pad7 pad2 : list byte) (p0 R : Z) (bs : list byte)
    (mb : byte) (d0 : pst) (m0 : mem) (mo0 : Model) : config -> Prop :=
  fun cf => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m' (errv' : word) (s' : as_St H) (d : pst) (q : Z) (E' : ecv) (XS : list (Z * Z)),
    as_VIS H s' (cfg_ms cf) = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (wz (q - p0)) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                                 F (ret_pc ra) fc None m' (seg_rom bsegs)
    /\ as_AKREL H s' cf /\ as_MPRES H mo0 (cfg_model cf)
    /\ mem_inv bsegs m' /\ stk bsegs m' lo (bv_unsigned sp)
    /\ rw_cells bsegs m' (errno_addr tp) [C4 errv'] /\ as_rauxv_ok H m' B
    /\ as_RHEAP H s' (ps_LBn d ++ LB0) m'
    /\ rw_cells bsegs m' P (ParserCoreCells (ps_c d) pad7 pad2)
    /\ rw_cells bsegs m' E (ErrCodeCells E') /\ (E' = EC_clear \/ http_fail E')
    /\ rw_cells bsegs m' (P + 240) [C1 (ps_rdi d)] /\ AHttpCat m' (ps_g d) /\ (AFieldTabZero m' \/ FT m')
    /\ PutU P p0 bs mb d m' /\ HdrOwnA (ps_LBn d ++ LB0) m' (ps_h d)
    /\ PutL sp P E p0 bs LB0 (ps_L d0) (ps_es d0) (ps_h d0) d /\ PutB LB0 p0 R d q
    /\ Forall (fs_scratch H LF) XS
    /\ xpres H LB0 (bv_unsigned sp) (put_X P E (ps_L d0) (ps_es d0) ++ XS) m0 m'
    /\ p0 <= q <= p0 + Z.of_nat (length bs)
    /\ (E' = EC_clear -> p0 < q \/ pc_state (ps_c d) = 11)
    /\ (pc_state (ps_c d) = 11 -> E' = EC_clear)
    /\ HdrDisjP (ps_em d) (ps_h d) /\ BodyDisjP (ps_em d) (ps_h d) (ps_es d)
    (* [comment removed for export] *)
    /\ as_RFS H LF m' /\ ACONST m' /\ stack0 m' lo shi
    /\ al_ok H s' (ps_A d) MA MR /\ ps_A d0 <= ps_A d.

Definition bput_stmt : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (msF : machine_state) (m : mem) (mo : Model)
         (s : as_St H) (LB0 : list block) (LF : list fframe) (P E lo B shi : Z) (pad7 pad2 ej : list byte) (p0 R : Z) (bs : list byte)
         (mb : byte) (d : pst) (errv : word),
    as_VIS H s msF = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                        F (Z_to_bv 64 P_A_BP_PUT) fc None m (seg_rom bsegs) ->
    a0 = wz P -> a1 = wz p0 -> a2 = wz (Z.of_nat (length bs)) -> a3 = wz E ->
    ps_LBn d = [] -> pc_state (ps_c d) <> 11 ->
    rw_cells bsegs m P (ParserCoreCells (ps_c d) pad7 pad2) ->
    rw_cells bsegs m E [CB 24 ej] ->
    rw_cells bsegs m (P + 240) [C1 (ps_rdi d)] -> AHttpCat m (ps_g d) -> (AFieldTabZero m \/ FT m) ->
    PutU P p0 bs mb d m -> HdrOwnA LB0 m (ps_h d) ->
    PutL sp P E p0 bs LB0 (ps_L d) (ps_es d) (ps_h d) d -> PutB LB0 p0 R d p0 ->
    put_static sp tp P E lo B shi p0 R bs ->
    as_RHEAP H s LB0 m -> as_AKREL H s (mkCfg msF mo) -> as_rauxv_ok H m B ->
    stk bsegs m lo (bv_unsigned sp) -> rw_cells bsegs m (errno_addr tp) [C4 errv] ->
    mem_inv bsegs m -> bv_unsigned ra mod 2 = 0 ->
    (* [comment removed for export] *)
    aobj LB0 LF P PARSER_SIZE -> accessible m P PARSER_SIZE ->
    aobj LB0 LF E 24 -> accessible m E 24 -> shvis m E (E + 24) ->
    aobj LB0 LF p0 (Z.of_nat (length bs)) -> accessible m p0 (Z.of_nat (length bs)) -> shvis m p0 (p0 + Z.of_nat (length bs)) ->
    as_RFS H LF m -> (length LF + 5 < AFS_MAXLIVE)%nat (* [comment removed for export] *) -> (length LF + 1 < AFS7_MAXLIVE)%nat -> ACONST m ->
    stack0 m lo shi ->
    al_ok H s (ps_A d) MA MR ->
    bv_unsigned mb <= 1 ->    (* [comment removed for export] *)
    as_SR H (bput_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s LB0 LF P E lo B shi pad7 pad2 p0 R bs mb d m mo)
      (mkCfg msF mo).

End HCW.
