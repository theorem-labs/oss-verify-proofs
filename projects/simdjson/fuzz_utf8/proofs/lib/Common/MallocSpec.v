(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common Require Import PropExec CatExec CatSim SeqExec StoreOk Hoare Frame RefMemcpyLib. From OSSVerify.Proofs.simdjson.fuzz_utf8.lib Require Import MallocDefs ImgParams.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. (* [comment removed for export] *)
Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
Definition tbl_clear (sct : Z) (m : word -> option byte) : Prop :=
  forall j, (0 <= j < 96)%Z -> m (Z_to_bv 64 (sct + j)) = None.

Section Generic.
  Context {fx : FPState}.
  Variable segs : list Segment.
  Variable sct secret : Z.

Record efH_g (mem : word -> option byte) (c : word)
       (g M W idx n h3 o16 stride start off : Z) : Prop := EFHG {
  Estride : stride = slot_stride (w_maplen W) (w_lastidx W) (w_sizeclass W);
  Estart  : start = slot_start M stride idx;
  Eoff    : off = enframe_off (slack_of stride n)
                    ((if h3 =? 0 then bv_unsigned c else o16 + 1) mod 256);
  Hg      : 0 <= g /\ g + 40 <= 2 ^ 64;
  HM      : 0 <= M;
  HW      : 0 <= W < 2 ^ 64;
  Hidx    : 0 <= idx < 32;
  Hn      : 0 <= n /\ n + 4 <= stride;
  Hsc     : (w_maplen W = 0 \/ w_lastidx W <> 0) -> w_sizeclass W < 48;
  Hst31   : stride < 2 ^ 31;
  Hq      : stride * idx + 4096 <= 16 * 65536;
  Hnw     : start + stride < 2 ^ 64;
  Hdisj   : g + 24 <= start - 3 \/ start + stride - 4 <= g + 16;
  Hh3     : 0 <= h3 < 256;
  Ho16    : 0 <= o16 < 65536;
  RM      : rdn segs mem (Z_to_bv 64 (g + 16)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 M));
  RW      : rdn segs mem (Z_to_bv 64 (g + 32)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 W));
  R4      : mem (Z_to_bv 64 (start - 4)) = Some (Z_to_bv 8 0);
  R3      : mem (Z_to_bv 64 (start - 3)) = Some (Z_to_bv 8 h3);
  R2      : h3 <> 0 ->
            rdn segs mem (Z_to_bv 64 (start - 2)) 2 = Some (word_to_le_bytes 2 (Z_to_bv 64 o16));
  OK      : store_ok segs mem (Z_to_bv 64 (start - 3)) (Z.to_nat (stride - 1)) = true;
  TBL     : tbl_clear sct mem }.

Record enframe_post_g (mem' : word -> option byte) (idx n stride start off : Z) : Prop := EPOSTG {
  P_p := start + 16 * off;
  P_e := start + stride - 4;
  P_r := stride - 4 - n - 16 * off;
  P_q := stride * idx / 16 + off;
  Pm4   : mem' (Z_to_bv 64 (P_p - 4)) = Some (Z_to_bv 8 0);
  Pm3   : mem' (Z_to_bv 64 (P_p - 3)) = Some (Z_to_bv 8 (idx + 32 * res_code P_r));
  Pm2   : rdn segs mem' (Z_to_bv 64 (P_p - 2)) 2 = Some (word_to_le_bytes 2 (Z_to_bv 64 P_q));
  Pzr   : 0 < P_r -> mem' (Z_to_bv 64 (P_p + n)) = Some (Z_to_bv 8 0);
  Pe5   : 5 <= P_r -> mem' (Z_to_bv 64 (P_e - 5)) = Some (Z_to_bv 8 0);
  Pe4   : 5 <= P_r -> rdn segs mem' (Z_to_bv 64 (P_e - 4)) 4 = Some (word_to_le_bytes 4 (Z_to_bv 64 P_r));
  Ps3   : off <> 0 -> mem' (Z_to_bv 64 (start - 3)) = Some (Z_to_bv 8 224);
  Ps2   : off <> 0 -> rdn segs mem' (Z_to_bv 64 (start - 2)) 2 = Some (word_to_le_bytes 2 (Z_to_bv 64 off));
  Pr    : 0 <= P_r /\ 0 <= off <= 255 /\ 0 <= P_q < 65536 }.

Record free_pre_g (mem : word -> option byte)
       (sp p e M g idx off n stride reserved q W avail freed : Z) (sec : word) : Prop := FPREG {
  (* [comment removed for export] *)
  fp_stride : stride = slot_stride (w_maplen W) (w_lastidx W) (w_sizeclass W);
  fp_p      : p = (M + 16 + stride * idx + 16 * off)%Z;
  fp_e      : e = (M + 16 + stride * idx + stride - 4)%Z;
  fp_res    : reserved = (stride - 4 - n - 16 * off)%Z;
  fp_q      : q = (stride * idx / 16 + off)%Z;
  (* [comment removed for export] *)
  fp_al     : (p mod 16 = 0)%Z;
  fp_M      : (0 <= M)%Z;
  fp_idx    : (0 <= idx <= w_lastidx W)%Z;
  fp_off    : (0 <= off)%Z;
  fp_n      : (0 <= n)%Z;
  fp_resr   : (0 <= reserved < 2^32)%Z;
  fp_q16    : (q < 65536)%Z;
  fp_W      : (0 <= W < 2^64)%Z;
  fp_g      : (0 <= g)%Z;
  fp_sc     : ((w_sizeclass W < 48 /\ size_class (w_sizeclass W) * idx <= q
                /\ q < size_class (w_sizeclass W) * (idx + 1))
               \/ (w_sizeclass W = 63 /\ w_maplen W <> 0 /\ w_lastidx W = 0))%Z;
  fp_ml     : (w_maplen W <> 0 -> q <= w_maplen W * 256 - 1)%Z;
  fp_av     : (0 <= avail < 2^32)%Z;  fp_avb : Z.testbit avail idx = false;
  fp_fr     : (0 <= freed < 2^32)%Z;  fp_frb : Z.testbit freed idx = false;
  (* [comment removed for export] *)
  fp_sp     : (sp < 2^64)%Z;
  fp_hi     : (e + 4 <= sp - 48 /\ g + 40 <= sp - 48 /\ secret + 8 <= sp - 48)%Z;
  fp_sok    : store_ok segs mem (Z_to_bv 64 (sp - 48)) 48%nat = true;
  (* [comment removed for export] *)
  fp_m4  : mem (Z_to_bv 64 (p - 4)) = Some (Z_to_bv 8 0);
  fp_m3  : mem (Z_to_bv 64 (p - 3)) = Some (Z_to_bv 8 (idx + 32 * res_code reserved));
  fp_m2  : rdn segs mem (Z_to_bv 64 (p - 2)) 2%nat = Some (word_to_le_bytes 2 (Z_to_bv 64 q));
  fp_zr  : (0 < reserved)%Z -> mem (Z_to_bv 64 (p + n)) = Some (Z_to_bv 8 0);
  fp_e5  : (5 <= reserved)%Z -> mem (Z_to_bv 64 (e - 5)) = Some (Z_to_bv 8 0);
  fp_e4  : (5 <= reserved)%Z ->
           rdn segs mem (Z_to_bv 64 (e - 4)) 4%nat = Some (word_to_le_bytes 4 (Z_to_bv 64 reserved));
  fp_end : mem (Z_to_bv 64 e) = Some (Z_to_bv 8 0);
  (* [comment removed for export] *)
  fp_meta : rdn segs mem (Z_to_bv 64 M) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 g));
  fp_mem  : rdn segs mem (Z_to_bv 64 (g + 16)) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 M));
  fp_Wm   : rdn segs mem (Z_to_bv 64 (g + 32)) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 W));
  fp_avm  : rdn segs mem (Z_to_bv 64 (g + 24)) 4%nat = Some (word_to_le_bytes 4 (Z_to_bv 64 avail));
  fp_frm  : rdn segs mem (Z_to_bv 64 (g + 28)) 4%nat = Some (word_to_le_bytes 4 (Z_to_bv 64 freed));
  fp_area : rdn segs mem (Z_to_bv 64 (g - g mod 4096)) 8%nat = Some (word_to_le_bytes 8 sec);
  fp_secm : rdn segs mem (Z_to_bv 64 secret) 8%nat = Some (word_to_le_bytes 8 sec);
  fp_img  : tbl_clear sct mem
}.
End Generic.

Section Stmts.
  Context {fx : FPState}.
  Variable ip : imgparams.
  #[local] Notation segs := (ip_segs ip).
  #[local] Notation MTB := (ip_M ip).

  (* [comment removed for export] *)
  Definition ENFRAME_STMT : Prop :=
    forall regs mem rom (ret c : word) (g M W idx n h3 o16 stride start off : Z),
      efH_g segs (mt_sct MTB) mem c g M W idx n h3 o16 stride start off ->
      getr regs 1%bv = ret -> ret_ok ret ->
      getr regs 10%bv = Z_to_bv 64 g -> getr regs 11%bv = Z_to_bv 64 idx ->
      getr regs 12%bv = Z_to_bv 64 n -> getr regs 13%bv = c ->
      exists regs' mem',
        msteps segs (mkst regs (Z_to_bv 64 (mt_enframe MTB)) mem rom) (mkst regs' ret mem' rom)
        /\ keeps_cs regs regs'
        /\ getr regs' 10%bv = Z_to_bv 64 (start + 16 * off)
        /\ frame_mod mem mem' [(Z_to_bv 64 (start - 3), stride - 1)]
        /\ enframe_post_g segs mem' idx n stride start off
        /\ frame_mod mem mem' [(Z_to_bv 64 (start - 3), 16 * off + 3); (Z_to_bv 64 (start + 16 * off + n), stride - 4 - n - 16 * off)].

  (* [comment removed for export] *)
  Definition free_mem1 (mem : word -> option byte) (sp : Z) (ra s0 s1 s2 s3 : word) : word -> option byte :=
    wbytes (wbytes (wbytes (wbytes (wbytes mem
      (Z_to_bv 64 (sp - 8)) (word_to_le_bytes 8 ra))
      (Z_to_bv 64 (sp - 16)) (word_to_le_bytes 8 s0))
      (Z_to_bv 64 (sp - 24)) (word_to_le_bytes 8 s1))
      (Z_to_bv 64 (sp - 32)) (word_to_le_bytes 8 s2))
      (Z_to_bv 64 (sp - 40)) (word_to_le_bytes 8 s3).
  Definition FREEPRO_STMT : Prop :=
    forall regs mem rom (sp p e M g idx off n stride reserved q W avail freed : Z) (sec : word),
      free_pre_g segs (mt_sct MTB) (mt_secret MTB) mem sp p e M g idx off n stride reserved q W avail freed sec ->
      getr regs 2%bv = Z_to_bv 64 sp -> getr regs 10%bv = Z_to_bv 64 p ->
      exists regs',
        msteps segs (mkst regs (Z_to_bv 64 (mt_free MTB)) mem rom)
                    (mkst regs' (Z_to_bv 64 (mt_free_k MTB))
                          (free_mem1 mem sp (getr regs 1%bv) (getr regs 8%bv) (getr regs 9%bv) (getr regs 18%bv) (getr regs 19%bv)) rom)
        /\ getr regs' 2%bv = Z_to_bv 64 (sp - 48)
        /\ getr regs' 9%bv = Z_to_bv 64 p
        /\ getr regs' 8%bv = Z_to_bv 64 idx
        /\ getr regs' 10%bv = Z_to_bv 64 g
        /\ getr regs' 11%bv = Z_to_bv 64 W
        /\ getr regs' 14%bv = Z_to_bv 64 reserved
        /\ getr regs' 15%bv = Z_to_bv 64 (e - 12)
        /\ getr regs' 18%bv = getr regs 18%bv /\ getr regs' 19%bv = getr regs 19%bv
        /\ getr regs' 3%bv = getr regs 3%bv /\ getr regs' 4%bv = getr regs 4%bv
        /\ getr regs' 20%bv = getr regs 20%bv /\ getr regs' 21%bv = getr regs 21%bv /\ getr regs' 22%bv = getr regs 22%bv /\ getr regs' 23%bv = getr regs 23%bv
        /\ getr regs' 24%bv = getr regs 24%bv /\ getr regs' 25%bv = getr regs 25%bv /\ getr regs' 26%bv = getr regs 26%bv /\ getr regs' 27%bv = getr regs 27%bv.
End Stmts.
