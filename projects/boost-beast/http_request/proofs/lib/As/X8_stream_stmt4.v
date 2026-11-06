(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.boost_beast.http_request.lib Require Import HeapCeil.
From OSSVerify.Proofs.boost_beast.http_request.lib.Lib Require Import Tac Image ZBridge SysStep SFModel CellsX Arr TacX Bytes Exec.
From OSSVerify.Proofs.boost_beast.http_request.lib.Spec Require Import Prelim.
From OSSVerify.Proofs.boost_beast.http_request.lib.As Require Import ASegs AsShadow AsConst AsIface AsIface5 AsIface6 AsIface7 AsCXXHeap AsWalk AsStack0 AXPres AXKit AXRep AXRep2 AsTRList.
From OSSVerify.Proofs.boost_beast.http_request.lib.As Require Import X8Kit X8SRKit X8_A_leaves2 XL_mutex XL_cond X8_cobj X8_S_place X8_stream_stmt.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition AFB_PREPARE_STACK : Z := 240 + AOPNEW_STACK.
(* [comment removed for export] *)
Definition ADBP_STACK : Z := 96 + AFB_PREPARE_STACK.
(* [comment removed for export] *)
Definition AREADSOME_STACK : Z := 176 + AINTRIN_STACK.

Definition ADBP_RET1 : Z := 0xcc574.       (* [comment removed for export] *)
Definition AFBP_DEL_RET : Z := 0xc0988.    (* [comment removed for export] *)

(* [comment removed for export] *)
Definition AW_MISC_CAT_VT48 : Z := AW_MISC_CAT_VPTR + 48.
(* [comment removed for export] *)
Definition ALOC_TS_EOF : Z := 0x117d58.
Definition EC_ts_eof_a : ecv := ec_make_loc ASIO_ERR_EOF AG_MISC_CAT_INST ALOC_TS_EOF.   (* [comment removed for export] *)

(* [comment removed for export] *)
Definition fbp_wild (cm : option (list (Z * Z))) : bool := match cm with Some _ => false | None => true end.

(* [comment removed for export] *)
Definition fbp_X (fb : Z) (FB : fbv) : list (Z * Z) :=
  [(fb, fb + SZ_FB); (fb_begin FB, fb_end FB); (sh (fb_begin FB), sh (fb_begin FB) + nsh (fb_cap FB))]%Z.

Section HCW.
  Context {HCEIL : HeapCeil}.

Definition AMiscVt48 (m : mem) : Prop := ro_cells asegs m AW_MISC_CAT_VT48 [C8 (wz P_A_ECAT_FAILED)].

(* [comment removed for export] *)
(* [comment removed for export] *)
Section W1.
  Variable H : asr.

(* [comment removed for export] *)
Definition fbp_chain (cm : option (list (Z * Z))) (m : mem) (s0v rav spv : Z) : Prop :=
  match cm with
  | Some CH => as_chain H m s0v CH /\ pf_ok (as_TR H) APF_c08e0 rav CH /\ (forall fp' ra', In (fp', ra') CH -> spv + 16 <= fp')
  | None => True
  end.

(* [comment removed for export] *)
Definition fbp_cost (FB : fbv) (n : Z) (wild : bool) : Z :=
  if fb_prep_inplace FB n || fb_prep_slide FB n then 0
  else as_Cm H (fb_newsize FB n)
       + (if fb_begin FB =? 0 then 0 else as_Cf H (fb_cap FB) + (if wild then ACWILD else 0)).

(* [comment removed for export] *)
Definition fb_prepare_rel (LB : list block) (FB : fbv) (n : Z) (LB' : list block) (FB' : fbv) : Prop :=
  if fb_prep_inplace FB n || fb_prep_slide FB n
  then FB' = fb_prep_small FB n /\ LB' = LB
  else exists (p' : bptr) (A' : Z),
         rblock_range A' (fb_newsize FB n) /\ FB' = fb_prep_grow FB n A'
      /\ ((FB = FB_empty /\ LB' = (p', A', fb_newsize FB n) :: LB)
          \/ (exists p, In (p, fb_begin FB, fb_cap FB) LB /\ LB' = (p', A', fb_newsize FB n) :: as_lb_remove H p LB)).

Definition fb_prepare_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (s : as_St H) (LB : list block) (LF : list fframe) (fb n lo B shi : Z) (FB : fbv) (ds : list byte) (cm : option (list (Z * Z)))
    (m : mem) (mo : Model) : config -> Prop :=
  fun c => exists t0 t1 t2 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m' (errv' : word) (s' : as_St H) (LB' : list block) (FB' : fbv) (XS : list (Z * Z)),
    as_VIS H s' (cfg_ms c) = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (wz (fb_out FB')) (wz n) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                                F (ret_pc ra) fc None m' (seg_rom asegs)
    /\ as_AKREL H s' c /\ as_MPRES H mo (cfg_model c)
    /\ mem_inv asegs m' /\ stk asegs m' lo (bv_unsigned sp)
    /\ rw_cells asegs m' (errno_addr tp) [C4 errv'] /\ as_rauxv_ok H m' B
    /\ as_RHEAP H s' LB' m'
    /\ AFlatBuf LB' m' fb FB' ds
    /\ fb_last FB' = fb_out FB' + n
    /\ fb_prepare_rel LB FB n LB' FB'
    /\ Forall (fs_scratch H LF) XS
    /\ xpres H LB (bv_unsigned sp) (fbp_X fb FB ++ XS) m m'
    /\ as_RFS H LF m' /\ ACONST m' /\ stack0 m' lo shi
    /\ as_AL H s' >= as_AL H s - fbp_cost FB n (fbp_wild cm).

(* [comment removed for export] *)
Definition fb_prepare_stmt : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (msF : machine_state) (m : mem) (mo : Model)
         (s : as_St H) (LB : list block) (LF : list fframe) (fb n lo B shi : Z) (FB : fbv) (ds : list byte) (errv : word)
         (cm : option (list (Z * Z))),
    as_VIS H s msF = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                        F (Z_to_bv 64 P_A_FB_PREPARE) fc None m (seg_rom asegs) ->
    a0 = wz fb -> a1 = wz n ->
    AFlatBuf LB m fb FB ds -> cobj LB LF (bv_unsigned sp) shi fb SZ_FB -> fb mod 8 = 0 -> accessible m fb SZ_FB ->
    0 <= n -> fb_size FB + n < 2^27 ->
    (fb + SZ_FB <= fb_begin FB \/ fb_end FB <= fb) ->
    as_RHEAP H s LB m -> as_AKREL H s (mkCfg msF mo) ->
    lb_bytes LB + fb_newsize FB n <= as_LIVE_MAX H -> Z.of_nat (length LB) + 1 <= as_LIVE_CNT_MAX H ->
    as_rauxv_ok H m B -> bv_unsigned sp <= B ->
    stk asegs m lo (bv_unsigned sp) -> aceil <= lo -> lo <= bv_unsigned sp - AFB_PREPARE_STACK ->
    rw_cells asegs m (errno_addr tp) [C4 errv] -> mem_inv asegs m -> tp = Z_to_bv 64 ATP ->
    bv_unsigned ra mod 2 = 0 ->
    (* [comment removed for export] *)
    bv_unsigned sp mod 16 = 0 ->
    as_RFS H LF m -> (length LF < AFS_MAXLIVE)%nat -> ACONST m ->
    stack0 m lo shi -> bv_unsigned sp <= shi ->
    fbp_chain cm m (bv_unsigned s0) (bv_unsigned ra) (bv_unsigned sp) -> 0 <= bv_unsigned s0 < 2^64 ->
    fbp_cost FB n (fbp_wild cm) <= as_AL H s ->
    as_SR H (fb_prepare_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s LB LF fb n lo B shi FB ds cm m mo)
      (mkCfg msF mo).
End W1.

(* [comment removed for export] *)
(* [comment removed for export] *)
Section W2.
  Variable H : asr.

Definition dbp_fb_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (s : as_St H) (LB : list block) (LF : list fframe) (OPT fb n ec lo B shi : Z) (FB : fbv) (ds oj : list byte)
    (m : mem) (mo : Model) : config -> Prop :=
  fun c => exists t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m' (errv' : word) (s' : as_St H) (LB' : list block) (FB' : fbv) (XS : list (Z * Z)),
    as_VIS H s' (cfg_ms c) = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                                F (ret_pc ra) fc None m' (seg_rom asegs)
    /\ as_AKREL H s' c /\ as_MPRES H mo (cfg_model c)
    /\ mem_inv asegs m' /\ stk asegs m' lo (bv_unsigned sp)
    /\ rw_cells asegs m' (errno_addr tp) [C4 errv'] /\ as_rauxv_ok H m' B
    /\ as_RHEAP H s' LB' m'
    /\ AFlatBuf LB' m' fb FB' ds
    /\ fb_last FB' = fb_out FB' + n
    /\ fb_prepare_rel H LB FB n LB' FB'
    /\ rw_cells asegs m' OPT [CB 1 [b8 1]; CB 7 (firstn 7 (skipn 1 oj)); C8 (wz (fb_out FB')); C8 (wz n)]
    /\ rw_cells asegs m' ec (ErrCodeCells EC_clear)
    /\ Forall (fs_scratch H LF) XS
    /\ xpres H LB (bv_unsigned sp) ((OPT, OPT + 24) :: (ec, ec + 24) :: fbp_X fb FB ++ XS) m m'
    /\ as_RFS H LF m' /\ ACONST m' /\ stack0 m' lo shi
    /\ as_AL H s' >= as_AL H s - fbp_cost H FB n true.

Definition dbp_fb_stmt : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (msF : machine_state) (m : mem) (mo : Model)
         (s : as_St H) (LB : list block) (LF : list fframe) (OPT fb n ec ev lo B shi : Z) (FB : fbv) (ds oj : list byte) (E : ecv) (errv : word),
    as_VIS H s msF = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                        F (Z_to_bv 64 P_A_FB_DYN_PREPARE) fc None m (seg_rom asegs) ->
    a0 = wz OPT -> a1 = wz fb -> a2 = wz n -> a3 = wz ec -> a4 = wz ev ->
    (* [comment removed for export] *)
    rw_cells asegs m OPT [CB 24 oj] -> OPT mod 8 = 0 -> bv_unsigned sp <= OPT -> OPT + 24 <= shi -> OPT + 24 <= B ->
    (* [comment removed for export] *)
    rw_cells asegs m ec (ErrCodeCells E) -> aobj LB LF ec 24 -> accessible m ec 24 ->
    (ec + 24 <= fb \/ fb + SZ_FB <= ec) -> (ec + 24 <= fb_begin FB \/ fb_end FB <= ec) -> (OPT + 24 <= fb \/ fb + SZ_FB <= OPT) ->
    (* [comment removed for export] *)
    AFlatBuf LB m fb FB ds -> cobj LB LF (bv_unsigned sp) shi fb SZ_FB -> fb mod 8 = 0 -> accessible m fb SZ_FB ->
    0 <= n -> fb_size FB + n < 2^27 ->
    (fb + SZ_FB <= fb_begin FB \/ fb_end FB <= fb) ->
    as_RHEAP H s LB m -> as_AKREL H s (mkCfg msF mo) ->
    lb_bytes LB + fb_newsize FB n <= as_LIVE_MAX H -> Z.of_nat (length LB) + 1 <= as_LIVE_CNT_MAX H ->
    as_rauxv_ok H m B -> bv_unsigned sp <= B ->
    stk asegs m lo (bv_unsigned sp) -> aceil <= lo -> lo <= bv_unsigned sp - ADBP_STACK ->
    rw_cells asegs m (errno_addr tp) [C4 errv] -> mem_inv asegs m -> tp = Z_to_bv 64 ATP ->
    bv_unsigned ra mod 2 = 0 ->
    (* [comment removed for export] *)
    bv_unsigned sp mod 16 = 0 ->
    as_RFS H LF m -> (length LF < AFS_MAXLIVE)%nat -> ACONST m ->
    stack0 m lo shi -> bv_unsigned sp <= shi ->
    fbp_cost H FB n true <= as_AL H s ->
    as_SR H (dbp_fb_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s LB LF OPT fb n ec lo B shi FB ds oj m mo)
      (mkCfg msF mo).
End W2.

(* [comment removed for export] *)
(* [comment removed for export] *)
Section W3.
  Variable H : asr.

Definition rs_W (lo : Z) (sp : word) (stb ec tgt tn ff fp : Z) : list (Z * Z) :=
  [(lo, bv_unsigned sp); (stb, stb + SZ_SPCI_STATE); (ec, ec + 24); (tgt, tgt + tn);
   (as_FSB H, as_FSB H + AFS_FLAGS); (fp, fp + 1); (ff, ff + 64); (sh ff, sh ff + 8)]%Z.

Definition readsome_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (LB : list block) (LF : list fframe) (stb ioc implb tgt tn ec lo shi : Z) (S : statev) (ds junk : list byte) (E : ecv) (m : mem)
    : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m' (ff fp : Z),
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (wz (rs_take ds tn)) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom asegs)
    /\ munch (rs_W lo sp stb ec tgt tn ff fp) m m' /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ stk asegs m' lo (bv_unsigned sp)
    /\ AStateBlock LB m' stb ioc implb (rs_state S ds tn) (skipn (Z.to_nat (rs_take ds tn)) ds)
    /\ rw_cells asegs m' tgt [CB (Z.to_nat (rs_take ds tn)) (firstn (Z.to_nat (rs_take ds tn)) ds);
                            CB (Z.to_nat (tn - rs_take ds tn)) (skipn (Z.to_nat (rs_take ds tn)) junk)]
    /\ rw_cells asegs m' ec (ErrCodeCells (if zlength ds =? 0 then EC_ts_eof_a else E))
    /\ AXStatics2 m' /\ AMiscVt48 m'
    /\ accessible m' tgt tn
    /\ fresh_frame H LF 0 ff fp /\ as_RFS H LF m' /\ ACONST m' /\ stack0 m' lo shi.

Definition readsome_stmt : Prop :=
  forall (bs stb ioc implb MB tgt tn ec lo shi : Z) (LB : list block) (LF : list fframe) (S : statev) (ds junk : list byte) (E : ecv)
    ra sp gp tp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : mem),
  (* [comment removed for export] *)
  ro_cells asegs m bs [C8 (wz (stb + O_SPC_STORAGE))] -> bs mod 8 = 0 ->
  (* [comment removed for export] *)
  AStateBlock LB m stb ioc implb S ds -> st_lk S = 0 -> (ds = [] -> st_code S = STREAM_EOF) ->
  st_nread S + 1 < 2^63 -> st_nread_bytes S + zlength ds < 2^63 ->
  (* [comment removed for export] *)
  ro_cells asegs m MB [C8 (wz tgt); C8 (wz tn)] -> MB mod 8 = 0 -> 1 <= tn < 2^40 ->
  rw_cells asegs m tgt [CB (Z.to_nat tn) junk] ->
  (* [comment removed for export] *)
  rw_cells asegs m ec (ErrCodeCells E) -> ec mod 8 = 0 ->
  (* [comment removed for export] *)
  AXStatics2 m -> AMiscVt48 m ->
  (* [comment removed for export] *)
  stk asegs m lo (bv_unsigned sp) -> lo + AREADSOME_STACK <= bv_unsigned sp -> aceil <= lo ->
  (* [comment removed for export] *)
  aapp tgt tn -> tgt + tn <= aceil ->
  (tgt + tn <= stb \/ stb + SZ_SPCI_STATE <= tgt) ->
  (st_fb S <> FB_empty -> tgt + tn <= fb_begin (st_fb S) \/ fb_end (st_fb S) <= tgt) ->
  (tgt + tn <= ec \/ ec + 24 <= tgt) -> (tgt + tn <= MB \/ MB + 16 <= tgt) ->
  (ec + 24 <= stb \/ stb + SZ_SPCI_STATE <= ec) -> (ec + 24 <= MB \/ MB + 16 <= ec) -> (ec + 24 <= bs \/ bs + 8 <= ec) ->
  (bs + 8 <= stb \/ stb + SZ_SPCI_STATE <= bs) -> (MB + 16 <= stb \/ stb + SZ_SPCI_STATE <= MB) -> (tgt + tn <= bs \/ bs + 8 <= tgt) ->
  (st_fb S <> FB_empty -> ec + 24 <= fb_begin (st_fb S) \/ fb_end (st_fb S) <= ec) ->
  (st_fb S <> FB_empty -> fb_end (st_fb S) <= stb \/ stb + SZ_SPCI_STATE <= fb_begin (st_fb S)) ->
  bv_unsigned ra mod 2 = 0 ->
  mem_inv asegs m ->
  (* [comment removed for export] *)
  bv_unsigned sp mod 16 = 0 -> tp = Z_to_bv 64 ATP -> ACONST m -> athr_cells m ->
  as_RFS H LF m -> (length LF < AFS_MAXLIVE)%nat ->
  stack0 m lo shi -> bv_unsigned sp <= shi ->
  aplace bs 8 -> fsobj H LF bs 8 -> accessible m bs 8 -> (bs + 8 <= lo \/ bv_unsigned sp <= bs) ->
  aplace MB 16 -> fsobj H LF MB 16 -> accessible m MB 16 -> (MB + 16 <= lo \/ bv_unsigned sp <= MB) ->
  aapp ec 24 -> fsobj H LF ec 24 -> accessible m ec 24 -> shvis m ec (ec + 24) -> (ec + 24 <= lo \/ bv_unsigned sp <= ec) ->
  fsobj H LF tgt tn -> accessible m tgt tn -> shvis m tgt (tgt + tn) ->
  fsobj H LF stb SZ_SPCI_STATE ->
  (st_fb S <> FB_empty -> fsobj H LF (fb_begin (st_fb S)) (fb_cap (st_fb S)) /\ shvis m (fb_begin (st_fb S)) (fb_end (st_fb S))) ->
  evt asegs (readsome_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc LB LF stb ioc implb tgt tn ec lo shi S ds junk E m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (wz bs) (wz MB) (wz ec) a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 P_A_STREAM_READ_SOME) fc None m (seg_rom asegs)).
End W3.

End HCW.
