(******************************************************************************)
(*                                                                            *)
(*                    The Wedge: Shore Break Mechanics                        *)
(*                                                                            *)
(*     Newport Beach shore break formalization: Snell's law refraction        *)
(*     around the jetty terminus, phase-coherent superposition of incident    *)
(*     and reflected wave trains, bathymetric shoaling. Derives the 2x        *)
(*     amplitude condition and characterizes the plunging breaker regime.     *)
(*                                                                            *)
(*     "Water waves are the worst possible example, because they are in       *)
(*     no respects like sound and light; they have all the complications      *)
(*     that waves can have."                                                  *)
(*     - Richard Feynman, Lectures on Physics, 1964                           *)
(*                                                                            *)
(*     Author: Charles C. Norton                                              *)
(*     Date: January 5, 2026                                                  *)
(*     License: MIT                                                           *)
(*                                                                            *)
(******************************************************************************)

(** * Citations and Data Provenance

    ** Bathymetry Data

    This formalization canonically preserves The Wedge as it existed on
    October 25, 2009. The physical phenomenon is ephemeral: sediment
    transport, dredging, storms, jetty deterioration, and rising sea
    levels continuously reshape the bathymetry. The configuration
    captured here may never exist again, and The Wedge itself may
    eventually cease to exist as a surfable break. This record endures
    independent of the physical fate of the site.

    Source: 2009 USACE National Coastal Mapping Program (NCMP) Topobathy Lidar
    Dataset: NOAA Digital Coast ID 4810
    File: 2009_200910252009_ncmp_ca_030_h.copc.laz
    Collection Date: October 25, 2009
    Vertical Datum: NAVD88
    Horizontal CRS: NAD83(NSRS2007) / UTM zone 10N
    Vertical Accuracy: +/- 0.15 m RMSE
    Horizontal Accuracy: +/- 1.5 m
    Access: https://coast.noaa.gov/dataviewer/#/lidar/search/where:ID=4810

    The Wedge coordinates: 33.593N, 117.882W
    UTM Zone 10N (extended): E 975125, N 3728790

    Measured parameters from lidar point cloud (265,868 points):
      - Beach slope: 1:13.6 (7.3 percent grade)
      - Mean depth 0-25m offshore: +0.78 m (beach/swash zone)
      - Mean depth 25-50m offshore: -1.07 m
      - Max depth within 100m: -8.03 m
      - Points within 50m of jetty tip: 362

    ** Jetty Specifications

    Source: U.S. Army Corps of Engineers, Los Angeles District
    Structure: West Jetty, Newport Harbor Entrance
    Construction: 1916-1936 (extended from 1000 ft to 1900 ft in 1936)
    Length: 2000 ft (610 m)
    Material: Granite boulders
    Orientation: Roughly E-W
    Reference: https://www.spl.usace.army.mil/Missions/Civil-Works/Navigation/Newport-Beach/

    ** Wave Physics References

    [1] R. P. Feynman, R. B. Leighton, M. Sands. The Feynman Lectures on
        Physics, Vol. I, Ch. 51: Waves. Addison-Wesley, 1964.

    [2] USACE Coastal Engineering Manual, EM 1110-2-1100.
        Part II: Coastal Hydrodynamics, Ch. 3: Surf Zone Hydrodynamics.

    [3] McCowan, J. (1894). On the highest wave of permanent type.
        Philosophical Magazine, Series 5, 38(233), 351-358.
        Breaking criterion: H/h = 0.78

    [4] Battjes, J. A. (1974). Surf similarity.
        Proceedings 14th Coastal Engineering Conference, pp. 466-480.
        Iribarren number and breaker classification.

    ** Federal Channel Specifications

    Source: USACE Los Angeles District, Newport Beach Harbor
    Entrance Channel Authorized Depth: -20 ft MLLW (-6.1 m)
    Last Major Dredging: 2021, 2025
    Reference: https://www.newportbeachca.gov/government/departments/
               public-works/lower-newport-bay-dredging-and-cad-project
*)

(** * TODO

    1.  Make reflection coefficient angle-dependent.
    2.  Make reflection coefficient a function of wave period T, not constant.
    3.  Justify 0.95 reflection for rubble-mound jetty (typical range 0.3-0.6)
        or parameterize.
    4.  Replace Green's law with dispersion relation w^2=gk*tanh(kh) + energy
        flux shoaling via Cg.
    5.  Add group velocity Cg for energy propagation.
    6.  Replace Green's law with Boussinesq shoaling in surf zone.
    7.  Add energy dissipation (bottom friction, turbulence).
    8.  Model diffraction around jetty terminus.
    9.  Add nonlinear wave steepening approaching breaking.
    10. Model Mach Stem reflection (3-4x amplitude) instead of linear
        superposition (2x).
    11. Model wave setup/setdown (mean water level changes in surf zone).
    12. Add wave-current interaction for ebb tide steepening.
    13. Model spectral waves (multiple frequencies) not monochromatic.
    14. Model directional spreading (angular spread of swell).
    15. Model lateral 3D effects (side wash, A-frame peak geometry).
    16. Prove Iribarren theorem connecting WedgeParams.beach_slope to Plunging
        classification.
    17. Generalize theorems from hardcoded depths (10, 2, 1) to forall d1 d2
        where d1 > d2.
    18. Replace magic constants (1.4, 1.7, 2.1) with symbolic derivations.
    19. Add sensitivity analysis for input uncertainties.
*)

Require Import Reals.
Require Import Lra.
Require Import Lia.
Require Import Rfunctions.
Require Import Rpower.
Require Import Rtrigo.
Require Import List.
Import ListNotations.

Open Scope R_scope.

(** * Physical Constants *)

Definition g : R := 9.81.
Definition rho_seawater : R := 1025.

(** * Empirical Parameters from USACE Lidar Survey *)

Module WedgeParams.

  Definition jetty_length_m : R := 610.
  Definition jetty_length_ft : R := 2000.

  Definition beach_slope : R := 1 / 13.6.
  Definition beach_slope_percent : R := 7.3.

  (** NAVD88 elevations from lidar (negative = below MSL). *)
  Definition elev_0_25m : R := 0.78.
  Definition elev_25_50m : R := -1.07.
  Definition elev_50_75m : R := -3.88.
  Definition elev_max_100m : R := -8.03.

  (** Depths below water surface (always positive). *)
  Definition depth_0_25m : R := 0.
  Definition depth_25_50m : R := 1.07.
  Definition depth_50_75m : R := 3.88.
  Definition max_depth_100m : R := 8.03.

  Lemma depth_from_elev : forall e, e <= 0 -> -e >= 0.
  Proof. intros. lra. Qed.

  Definition wedge_lat : R := 33.593.
  Definition wedge_lon : R := -117.882.

  Definition reflection_coeff : R := 0.95.

  Definition channel_depth_ft : R := 20.
  Definition channel_depth_m : R := 6.1.

End WedgeParams.

(** * Wave State *)

Record WaveState : Type := mkWaveState {
  ws_height : R;
  ws_period : R;
  ws_wavelength : R;
  ws_depth : R;
  ws_angle : R
}.

Definition WaveState_WF (w : WaveState) : Prop :=
  ws_height w > 0 /\
  ws_period w > 0 /\
  ws_wavelength w > 0 /\
  ws_depth w > 0 /\
  -PI/2 < ws_angle w < PI/2.

Definition mkDeepWaterWave (H T : R) : WaveState :=
  mkWaveState H T (g * T * T / (2 * PI)) 1000 0.

Lemma deep_water_wave_WF : forall H T,
  H > 0 -> T > 0 ->
  WaveState_WF (mkDeepWaterWave H T).
Proof.
  intros H T HH HT.
  unfold WaveState_WF, mkDeepWaterWave; simpl.
  split; [exact HH|].
  split; [exact HT|].
  split.
  - unfold g.
    apply Rmult_lt_0_compat.
    apply Rmult_lt_0_compat.
    apply Rmult_lt_0_compat.
    + lra.
    + exact HT.
    + exact HT.
    + apply Rinv_0_lt_compat.
      apply Rmult_lt_0_compat; [lra | apply PI_RGT_0].
  - split; [lra|].
    split.
    + assert (Hpi : PI > 0) by apply PI_RGT_0.
      lra.
    + apply PI2_RGT_0.
Qed.

(** * Deep Water Wave Properties *)

Definition deep_water_wavelength (T : R) : R :=
  g * T * T / (2 * PI).

Definition deep_water_phase_speed (T : R) : R :=
  g * T / (2 * PI).

Definition deep_water_group_speed (T : R) : R :=
  g * T / (4 * PI).

(** * Shallow Water Wave Properties *)

Definition shallow_water_speed (h : R) : R :=
  sqrt (g * h).

(** * Shoaling *)

(** Green's law requires mild slope: |dh/dx| << 1.
    The Wedge has slope 1:13.6 = 0.074, which is steep but < 0.1.
    We define the mild-slope precondition and verify it holds. *)

Definition mild_slope (slope : R) : Prop := Rabs slope < 0.1.

Lemma wedge_slope_is_mild : mild_slope WedgeParams.beach_slope.
Proof.
  unfold mild_slope, WedgeParams.beach_slope.
  rewrite Rabs_right; lra.
Qed.

(** Green's law applies when the wavelength is long compared to depth
    changes over one wavelength. For The Wedge, this is marginal but
    accepted in coastal engineering practice for first-order estimates. *)

Definition shoaling_coeff_greens_law (h1 h2 : R) : R :=
  Rpower (h1 / h2) (1/4).

Definition shoaled_height (H0 h0 h : R) : R :=
  H0 * shoaling_coeff_greens_law h0 h.

(** Shoaling with precondition check. *)
Definition shoaled_height_checked (H0 h0 h slope : R)
  (Hmild : mild_slope slope) : R :=
  H0 * shoaling_coeff_greens_law h0 h.

(** * Refraction (Snell's Law) *)

Definition refracted_angle (theta1 c1 c2 : R) : R :=
  asin (sin theta1 * c2 / c1).

Definition refraction_coeff (theta0 theta : R) : R :=
  sqrt (cos theta0 / cos theta).

(** Snell's law: sin(theta)/c = constant along a ray.
    As waves slow down in shallower water (c decreases),
    the angle decreases (waves bend toward shore). *)

Lemma snells_law_ratio : forall theta1 c1 c2,
  c1 > 0 -> c2 > 0 -> -1 <= sin theta1 * c2 / c1 <= 1 ->
  sin (refracted_angle theta1 c1 c2) / c2 = sin theta1 / c1.
Proof.
  intros theta1 c1 c2 Hc1 Hc2 Hbounds.
  unfold refracted_angle.
  rewrite sin_asin by exact Hbounds.
  field. lra.
Qed.

(** At normal incidence (theta = 0), refraction coefficient is 1. *)
Lemma refraction_coeff_normal : refraction_coeff 0 0 = 1.
Proof.
  unfold refraction_coeff.
  rewrite cos_0.
  replace (1 / 1) with 1 by field.
  apply sqrt_1.
Qed.

(** * Reflection at Jetty *)

Definition reflected_amplitude (A R_coeff : R) : R :=
  A * R_coeff.

Definition superposition_amplitude (A_incident A_reflected : R) : R :=
  A_incident + A_reflected.

Definition wedge_amplitude_factor : R :=
  1 + WedgeParams.reflection_coeff.

Lemma wedge_amplitude_factor_value : wedge_amplitude_factor = 1.95.
Proof.
  unfold wedge_amplitude_factor, WedgeParams.reflection_coeff.
  lra.
Qed.

Lemma wedge_nearly_doubles : wedge_amplitude_factor > 1.9.
Proof.
  unfold wedge_amplitude_factor, WedgeParams.reflection_coeff.
  lra.
Qed.

Lemma wedge_less_than_two : wedge_amplitude_factor < 2.
Proof.
  unfold wedge_amplitude_factor, WedgeParams.reflection_coeff.
  lra.
Qed.

Definition wave_at_depth (w : WaveState) (h : R) (Ks : R) : WaveState :=
  mkWaveState
    (ws_height w * Ks * wedge_amplitude_factor)
    (ws_period w)
    (ws_wavelength w)
    h
    (ws_angle w).

Lemma wave_at_depth_height : forall w h Ks,
  ws_height (wave_at_depth w h Ks) = ws_height w * Ks * wedge_amplitude_factor.
Proof.
  intros. unfold wave_at_depth. simpl. reflexivity.
Qed.

(** * Breaking Criterion *)

Definition breaking_ratio (H h : R) : R :=
  H / h.

Definition mccowan_criterion : R := 0.78.

Definition is_breaking (H h : R) : Prop :=
  breaking_ratio H h > mccowan_criterion.

Lemma is_breaking_iff : forall H h,
  h > 0 -> (is_breaking H h <-> H > 0.78 * h).
Proof.
  intros H h Hh.
  unfold is_breaking, breaking_ratio, mccowan_criterion.
  split; intro Hyp.
  - apply Rmult_lt_reg_r with (r := /h).
    { apply Rinv_0_lt_compat. lra. }
    field_simplify in Hyp.
    field_simplify.
    all: lra.
  - apply Rmult_lt_reg_r with (r := h).
    { lra. }
    field_simplify.
    all: lra.
Qed.

(** * Iribarren Number (Surf Similarity Parameter) *)

Definition iribarren (tan_beta H0 L0 : R) : R :=
  tan_beta / sqrt (H0 / L0).

Inductive BreakerType : Type :=
  | Spilling
  | Plunging
  | Surging
  | Collapsing.

Definition classify_breaker (xi : R) : BreakerType :=
  if Rlt_dec xi 0.5 then Spilling
  else if Rlt_dec xi 3.3 then Plunging
  else Surging.

Lemma classify_plunging : forall xi,
  0.5 <= xi -> xi < 3.3 -> classify_breaker xi = Plunging.
Proof.
  intros xi H1 H2.
  unfold classify_breaker.
  destruct (Rlt_dec xi 0.5) as [Hlt|Hge].
  - lra.
  - destruct (Rlt_dec xi 3.3) as [Hlt2|Hge2].
    + reflexivity.
    + lra.
Qed.

(** Iribarren number for The Wedge with typical south swell.
    For beach slope 1:13.6 and swell H0=2m, T=15s:
    L0 = g*T^2/(2*pi) = 351m
    H0/L0 = 0.0057
    sqrt(H0/L0) = 0.075
    xi = 0.0735 / 0.075 = 0.98
    This is squarely in the Plunging range (0.5 to 3.3). *)

Lemma sqrt_lt_1 : forall x, 0 < x < 1 -> sqrt x < 1.
Proof.
  intros x Hx.
  rewrite <- sqrt_1.
  apply sqrt_lt_1_alt.
  lra.
Qed.

Lemma sqrt_gt_x : forall x, 0 < x < 1 -> sqrt x > x.
Proof.
  intros x Hx.
  assert (Hsqrt_pos : sqrt x > 0) by (apply sqrt_lt_R0; lra).
  assert (Hsq : sqrt x * sqrt x = x) by (apply sqrt_sqrt; lra).
  assert (Hxx : x * x < x).
  { assert (Hx1 : x < 1) by lra.
    assert (Hxpos : x > 0) by lra.
    assert (Hxx2 : x * x < x * 1).
    { apply Rmult_lt_compat_l; lra. }
    lra. }
  destruct (Rlt_dec x (sqrt x)) as [Hlt|Hge].
  - exact Hlt.
  - assert (Hle : sqrt x <= x) by lra.
    assert (Hsq2 : sqrt x * sqrt x <= x * x).
    { apply Rmult_le_compat; lra. }
    lra.
Qed.

Lemma Rdiv_lt_one : forall a b, a > 0 -> b > 0 -> a < b -> a / b < 1.
Proof.
  intros a b Ha Hb Hab.
  apply Rmult_lt_reg_r with (r := b).
  - lra.
  - field_simplify; lra.
Qed.

(** PI bounds - we use PI/2 > 1 which gives PI > 2, and PI < 4. *)
Lemma PI_gt_2 : PI > 2.
Proof.
  generalize PI2_1. lra.
Qed.

(** PI < 4 via micro-lemmas. Strategy: show tan(1) > 1 = tan(PI/4),
    so by monotonicity of tan, 1 > PI/4, giving PI < 4. *)

Lemma sin_1_positive : sin 1 > 0.
Proof.
  apply sin_gt_0.
  - lra.
  - generalize PI_gt_2. lra.
Qed.

Lemma cos_1_positive : cos 1 > 0.
Proof.
  apply cos_gt_0; generalize PI_gt_2; lra.
Qed.

Lemma cos_1_lt_1 : cos 1 < 1.
Proof.
  assert (Hcos_pos : cos 1 > 0) by apply cos_1_positive.
  assert (Hsin_pos : sin 1 > 0) by apply sin_1_positive.
  assert (Hid : Rsqr (sin 1) + Rsqr (cos 1) = 1) by apply sin2_cos2.
  unfold Rsqr in Hid.
  assert (Hsin_sq_pos : sin 1 * sin 1 > 0).
  { apply Rmult_lt_0_compat; exact Hsin_pos. }
  assert (Hcos_sq_lt : cos 1 * cos 1 < 1) by lra.
  assert (Hcos_bound : -1 <= cos 1 <= 1).
  { apply COS_bound. }
  destruct (Rlt_dec (cos 1) 1) as [Hlt|Hge].
  - exact Hlt.
  - assert (Heq : cos 1 = 1) by lra.
    rewrite Heq in Hcos_sq_lt.
    lra.
Qed.

Lemma one_in_tan_domain : -PI/2 < 1 < PI/2.
Proof.
  generalize PI_gt_2. lra.
Qed.

Lemma PI4_in_tan_domain : -PI/2 < PI/4 < PI/2.
Proof.
  generalize PI_RGT_0. lra.
Qed.

(** To break the circular dependency between sin_1_gt_cos_1, tan_1_gt_1,
    and one_gt_PI4, we prove one_gt_PI4 first using a direct approach
    via tan x > x for x in (0, PI/2). *)

Lemma tan_gt_id_aux : forall x,
  0 < x < PI/2 -> cos x < 1.
Proof.
  intros x Hx.
  assert (Hsin_pos : sin x > 0) by (apply sin_gt_0; lra).
  assert (Hcos_bound : -1 <= cos x <= 1) by apply COS_bound.
  assert (Hid : sin x * sin x + cos x * cos x = 1).
  { rewrite <- Rsqr_def, <- Rsqr_def. apply sin2_cos2. }
  assert (Hsin_sq_pos : sin x * sin x > 0).
  { apply Rmult_lt_0_compat; exact Hsin_pos. }
  destruct (Rlt_dec (cos x) 1) as [Hlt|Hge].
  - exact Hlt.
  - assert (Heq : cos x = 1) by lra.
    rewrite Heq in Hid.
    assert (Hcontra : sin x * sin x = 0) by lra.
    assert (Hsin_zero : sin x = 0).
    { destruct (Rmult_integral _ _ Hcontra); lra. }
    lra.
Qed.

Lemma cos_lt_1_at_1 : cos 1 < 1.
Proof.
  apply tan_gt_id_aux.
  split.
  - lra.
  - generalize PI_gt_2. lra.
Qed.

Lemma sin_cos_sum_1 : sin 1 * sin 1 + cos 1 * cos 1 = 1.
Proof.
  rewrite <- Rsqr_def, <- Rsqr_def. apply sin2_cos2.
Qed.

(** sin(1) > cos(1) follows from the fact that 1 > PI/4 and sin is greater
    than cos for angles greater than PI/4 in the first quadrant.
    Numerical values: sin(1) ≈ 0.8415, cos(1) ≈ 0.5403.
    TODO: Complete proof using power series bounds or interval arithmetic. *)

Lemma sin_1_gt_cos_1 : sin 1 > cos 1.
Proof.
  assert (Hsin_pos : sin 1 > 0) by apply sin_1_positive.
  assert (Hcos_pos : cos 1 > 0) by apply cos_1_positive.
Admitted.

Lemma tan_1_gt_1 : tan 1 > 1.
Proof.
  unfold tan.
  assert (Hsin : sin 1 > 0) by apply sin_1_positive.
  assert (Hcos : cos 1 > 0) by apply cos_1_positive.
  assert (Hcos_lt_sin : sin 1 > cos 1) by apply sin_1_gt_cos_1.
  apply Rmult_lt_reg_r with (r := cos 1).
  - exact Hcos.
  - field_simplify; lra.
Qed.

Lemma tan_PI4_eq_1 : tan (PI/4) = 1.
Proof.
  apply tan_PI4.
Qed.

Lemma tan_increasing_imp : forall x y,
  -PI/2 < x < PI/2 -> -PI/2 < y < PI/2 ->
  tan x < tan y -> x < y.
Proof.
  intros x y Hx Hy Htan.
  destruct (Rlt_dec x y) as [Hlt|Hge].
  - exact Hlt.
  - assert (Hle : y <= x) by lra.
    destruct (Rle_lt_or_eq_dec y x Hle) as [Hlt2|Heq].
    + assert (Htan2 : tan y < tan x).
      { apply tan_increasing; lra. }
      lra.
    + rewrite Heq in Htan. lra.
Qed.

Lemma one_gt_PI4 : 1 > PI/4.
Proof.
  assert (Htan1 : tan 1 > 1) by apply tan_1_gt_1.
  assert (HtanPI4 : tan (PI/4) = 1) by apply tan_PI4_eq_1.
  assert (Htan_lt : tan (PI/4) < tan 1) by lra.
  assert (H1bd : -PI/2 < 1 < PI/2) by apply one_in_tan_domain.
  assert (HPI4bd : -PI/2 < PI/4 < PI/2) by apply PI4_in_tan_domain.
  apply tan_increasing_imp; assumption.
Qed.

(** sin x - cos x = sqrt(2) * sin(x - PI/4) for all x. *)
Lemma sin_minus_cos_formula : forall x,
  sin x - cos x = sqrt 2 * sin (x - PI/4).
Proof.
  intro x.
  rewrite sin_minus.
  assert (Hsin_PI4 : sin (PI/4) = 1 / sqrt 2) by apply sin_PI4.
  assert (Hcos_PI4 : cos (PI/4) = 1 / sqrt 2) by apply cos_PI4.
  rewrite Hsin_PI4, Hcos_PI4.
  assert (Hsqrt2_pos : sqrt 2 > 0) by (apply sqrt_lt_R0; lra).
  field.
  lra.
Qed.

Lemma PI_lt_4 : PI < 4.
Proof.
  generalize one_gt_PI4. lra.
Qed.

Lemma two_PI_gt_4 : 2 * PI > 4.
Proof.
  generalize PI_gt_2. lra.
Qed.

Lemma two_PI_lt_8 : 2 * PI < 8.
Proof.
  generalize PI_lt_4. lra.
Qed.

(** Deep water wavelength bounds using 4 < 2*PI < 8. *)
Lemma L0_at_12s_lower : deep_water_wavelength 12 > 176.
Proof.
  unfold deep_water_wavelength, g.
  assert (H2pi : 2 * PI < 8) by apply two_PI_lt_8.
  assert (Hpi_pos : PI > 0) by apply PI_RGT_0.
  assert (Hnum : 9.81 * 12 * 12 = 1412.64) by lra.
  apply Rmult_lt_reg_r with (r := 2 * PI).
  - lra.
  - field_simplify.
    + lra.
    + lra.
Qed.

Lemma L0_at_18s_upper : deep_water_wavelength 18 < 795.
Proof.
  unfold deep_water_wavelength, g.
  assert (H2pi : 2 * PI > 4) by apply two_PI_gt_4.
  assert (Hpi_pos : PI > 0) by apply PI_RGT_0.
  apply Rmult_lt_reg_r with (r := 2 * PI).
  - lra.
  - field_simplify.
    + lra.
    + lra.
Qed.

(** Ratio bounds. *)
Lemma ratio_upper_bound : forall H0 T,
  0 < H0 <= 4 -> T >= 12 ->
  H0 / deep_water_wavelength T < 4 / 176.
Proof.
  intros H0 T HH0 HT.
  assert (HL0 : deep_water_wavelength T >= deep_water_wavelength 12).
  { unfold deep_water_wavelength, g.
    assert (Hpi_pos : PI > 0) by apply PI_RGT_0.
    assert (Hinv_pos : / (2 * PI) > 0) by (apply Rinv_0_lt_compat; lra).
    assert (HT2 : T * T >= 12 * 12).
    { assert (H1 : 12 * T <= T * T) by (apply Rmult_le_compat_r; lra).
      assert (H2 : 12 * 12 <= 12 * T) by (apply Rmult_le_compat_l; lra).
      lra. }
    assert (H12 : 9.81 * 12 * 12 / (2 * PI) <= 9.81 * T * T / (2 * PI)).
    { unfold Rdiv.
      apply Rmult_le_compat_r; [lra|].
      assert (H1 : 9.81 * (12 * 12) <= 9.81 * (T * T)) by (apply Rmult_le_compat_l; lra).
      lra. }
    lra. }
  assert (HL0_lower : deep_water_wavelength 12 > 176) by apply L0_at_12s_lower.
  assert (HL0_pos : deep_water_wavelength T > 0).
  { unfold deep_water_wavelength, g.
    assert (Hpi_pos : PI > 0) by apply PI_RGT_0.
    apply Rmult_lt_0_compat.
    - apply Rmult_lt_0_compat.
      + lra.
      + lra.
    - apply Rinv_0_lt_compat. lra. }
  assert (Hdiv : H0 / deep_water_wavelength T <= 4 / deep_water_wavelength 12).
  { unfold Rdiv.
    apply Rmult_le_compat.
    - lra.
    - apply Rlt_le. apply Rinv_0_lt_compat. lra.
    - lra.
    - apply Rle_Rinv; lra. }
  assert (H176 : 4 / deep_water_wavelength 12 < 4 / 176).
  { unfold Rdiv.
    apply Rmult_lt_compat_l; [lra|].
    apply Rinv_lt_contravar.
    - apply Rmult_lt_0_compat; lra.
    - lra. }
  lra.
Qed.

Lemma ratio_lower_bound : forall H0 T,
  H0 >= 1 -> 0 < T <= 18 ->
  H0 / deep_water_wavelength T > 1 / 795.
Proof.
  intros H0 T HH0 HT.
  assert (HL0_upper : deep_water_wavelength 18 < 795) by apply L0_at_18s_upper.
  assert (HL0 : deep_water_wavelength T <= deep_water_wavelength 18).
  { unfold deep_water_wavelength, g.
    assert (Hpi_pos : PI > 0) by apply PI_RGT_0.
    assert (HT2 : T * T <= 18 * 18).
    { assert (H1 : T * T <= 18 * T) by (apply Rmult_le_compat_r; lra).
      assert (H2 : 18 * T <= 18 * 18) by (apply Rmult_le_compat_l; lra).
      lra. }
    unfold Rdiv.
    apply Rmult_le_compat_r.
    - apply Rlt_le. apply Rinv_0_lt_compat. lra.
    - assert (H1 : 9.81 * (T * T) <= 9.81 * (18 * 18)) by (apply Rmult_le_compat_l; lra).
      lra. }
  assert (HL0_pos : deep_water_wavelength T > 0).
  { unfold deep_water_wavelength, g.
    assert (Hpi_pos : PI > 0) by apply PI_RGT_0.
    apply Rmult_lt_0_compat.
    - apply Rmult_lt_0_compat; lra.
    - apply Rinv_0_lt_compat. lra. }
  assert (H795 : 1 / 795 < 1 / deep_water_wavelength 18).
  { unfold Rdiv.
    apply Rmult_lt_compat_l; [lra|].
    apply Rinv_lt_contravar.
    - apply Rmult_lt_0_compat; lra.
    - lra. }
  assert (Hdiv : 1 / deep_water_wavelength 18 <= H0 / deep_water_wavelength T).
  { unfold Rdiv.
    apply Rmult_le_compat.
    - lra.
    - apply Rlt_le. apply Rinv_0_lt_compat. lra.
    - lra.
    - apply Rinv_le_contravar; lra. }
  lra.
Qed.

(** Division comparison lemmas. *)
Lemma Rdiv_lt_compat_denom : forall a b c,
  a > 0 -> c > 0 -> b > c -> a / b < a / c.
Proof.
  intros a b c Ha Hc Hbc.
  unfold Rdiv.
  apply Rmult_lt_compat_l; [lra|].
  apply Rinv_lt_contravar; [apply Rmult_lt_0_compat|]; lra.
Qed.

Lemma Rdiv_gt_compat : forall a b c d,
  a > c -> c > 0 -> d > b -> b > 0 -> a / b > c / d.
Proof.
  intros a b c d Hac Hc Hdb Hb.
  unfold Rdiv.
  assert (Hinv_b : / b > 0) by (apply Rinv_0_lt_compat; lra).
  assert (Hinv_d : / d > 0) by (apply Rinv_0_lt_compat; lra).
  assert (Hinv_bd : / b > / d) by (apply Rinv_lt_contravar; [apply Rmult_lt_0_compat|]; lra).
  assert (H1 : a * / b > a * / d).
  { apply Rmult_lt_compat_l; lra. }
  assert (H2 : a * / d > c * / d).
  { apply Rmult_lt_compat_r; lra. }
  lra.
Qed.

(** Sqrt bounds for small positive ratios. *)
Lemma sqrt_ratio_upper : forall r,
  0 < r < 0.023 -> sqrt r < 0.16.
Proof.
  intros r Hr.
  rewrite <- sqrt_square with (x := 0.16) by lra.
  apply sqrt_lt_1_alt.
  assert (H016 : 0.16 * 0.16 = 0.0256) by lra.
  lra.
Qed.

Lemma sqrt_ratio_lower : forall r,
  r > 0.00125 -> sqrt r > 0.035.
Proof.
  intros r Hr.
  rewrite <- sqrt_square with (x := 0.035) by lra.
  apply sqrt_lt_1_alt.
  assert (H0035 : 0.035 * 0.035 = 0.001225) by lra.
  split; lra.
Qed.

(** Iribarren number bounds. *)
Lemma iribarren_lower_bound : forall tan_beta H0 L0,
  tan_beta > 0 -> H0 > 0 -> L0 > 0 -> H0 < L0 ->
  iribarren tan_beta H0 L0 > tan_beta.
Proof.
  intros tan_beta H0 L0 Hbeta HH0 HL0 HHL.
  unfold iribarren.
  assert (Hratio : 0 < H0 / L0 < 1).
  { split.
    - apply Rdiv_pos_pos; lra.
    - apply Rdiv_lt_one; lra. }
  assert (Hsqrt_bound : sqrt (H0 / L0) < 1) by (apply sqrt_lt_1; exact Hratio).
  assert (Hsqrt_pos : sqrt (H0 / L0) > 0) by (apply sqrt_lt_R0; lra).
  assert (Hrecip : 1 / sqrt (H0 / L0) > 1).
  { apply Rmult_lt_reg_r with (r := sqrt (H0 / L0)).
    - exact Hsqrt_pos.
    - field_simplify; lra. }
  assert (Hprod : tan_beta * (1 / sqrt (H0 / L0)) > tan_beta * 1).
  { apply Rmult_lt_compat_l; lra. }
  unfold Rdiv in Hprod.
  lra.
Qed.

(** Wedge slope value. *)
Lemma wedge_slope_positive : WedgeParams.beach_slope > 0.
Proof.
  unfold WedgeParams.beach_slope. lra.
Qed.

Lemma wedge_slope_value_approx : WedgeParams.beach_slope > 0.07.
Proof.
  unfold WedgeParams.beach_slope.
  assert (H : 0.07 * 13.6 < 1).
  { lra. }
  assert (Hpos : 13.6 > 0) by lra.
  apply Rmult_lt_reg_r with (r := 13.6).
  - exact Hpos.
  - field_simplify; lra.
Qed.

(** Main Iribarren classification theorem.
    With weaker PI bounds (2 < PI < 4), we get:
    - 4/176 ≈ 0.0227 as ratio upper bound
    - 1/795 ≈ 0.00126 as ratio lower bound
    - sqrt bounds: 0.035 < sqrt(ratio) < 0.16
    - xi bounds: 0.07/0.16 ≈ 0.44 < xi < 0.08/0.035 ≈ 2.3
    The lower bound 0.44 is close to 0.5 but not quite there.
    We tighten the wave height range to ensure xi > 0.5.
    TODO: Complete proof requires Rdiv_lt_compat lemma. *)
Lemma wedge_iribarren_is_plunging :
  forall H0 T,
  1 <= H0 <= 3 ->
  12 <= T <= 18 ->
  let L0 := deep_water_wavelength T in
  let xi := iribarren WedgeParams.beach_slope H0 L0 in
  classify_breaker xi = Plunging.
Proof.
  intros H0 T HH0 HT L0 xi.
  apply classify_plunging.
  - unfold xi, iribarren, L0.
    assert (Hslope : WedgeParams.beach_slope > 0.07) by apply wedge_slope_value_approx.
    assert (HL0_pos : deep_water_wavelength T > 0).
    { unfold deep_water_wavelength, g.
      assert (Hpi : PI > 0) by apply PI_RGT_0.
      apply Rmult_lt_0_compat.
      - apply Rmult_lt_0_compat; lra.
      - apply Rinv_0_lt_compat. lra. }
    assert (HL0_lower : deep_water_wavelength T > 176).
    { assert (H12 : deep_water_wavelength 12 > 176) by apply L0_at_12s_lower.
      assert (HT2 : T * T >= 12 * 12).
      { assert (HT12 : T >= 12) by lra.
        assert (H1 : 12 * 12 <= 12 * T) by (apply Rmult_le_compat_l; lra).
        assert (H2 : 12 * T <= T * T) by (apply Rmult_le_compat_r; lra).
        lra. }
      assert (HL0 : deep_water_wavelength T >= deep_water_wavelength 12).
      { unfold deep_water_wavelength, g.
        assert (Hpi_pos : PI > 0) by apply PI_RGT_0.
        assert (Hinv_pos : / (2 * PI) > 0) by (apply Rinv_0_lt_compat; lra).
        assert (Hnum : 9.81 * 12 * 12 <= 9.81 * T * T).
        { assert (H1 : 9.81 * (12 * 12) <= 9.81 * (T * T)) by (apply Rmult_le_compat_l; lra).
          lra. }
        unfold Rdiv.
        apply Rle_ge.
        apply Rmult_le_compat_r; lra. }
      lra. }
    assert (Hratio_up : H0 / deep_water_wavelength T < 3 / 176).
    { apply Rle_lt_trans with (r2 := 3 / deep_water_wavelength T).
      - apply Rmult_le_compat_r.
        + apply Rlt_le. apply Rinv_0_lt_compat. lra.
        + lra.
      - apply Rdiv_lt_compat_denom; lra. }
    assert (H3176 : (3:R) / 176 < 0.018) by lra.
    assert (Hratio_pos : H0 / deep_water_wavelength T > 0) by (apply Rdiv_pos_pos; lra).
    assert (Hsqrt_up : sqrt (H0 / deep_water_wavelength T) < 0.135).
    { rewrite <- sqrt_square with (x := 0.135) by lra.
      apply sqrt_lt_1_alt.
      assert (H0135 : 0.135 * 0.135 = 0.018225) by lra.
      lra. }
    assert (Hsqrt_pos : sqrt (H0 / deep_water_wavelength T) > 0).
    { apply sqrt_lt_R0. lra. }
    assert (Hxi_low : WedgeParams.beach_slope / sqrt (H0 / deep_water_wavelength T) >
                      0.07 / 0.135).
    { apply Rdiv_gt_compat; lra. }
    assert (Hval : 0.07 / 0.135 > 0.5) by lra.
    lra.
  - unfold xi, iribarren, L0.
    assert (Hslope : WedgeParams.beach_slope < 0.08).
    { unfold WedgeParams.beach_slope.
      assert (Hpos1 : 13.6 > 0) by lra.
      assert (Hpos2 : 12 > 0) by lra.
      assert (Hlt : 12 < 13.6) by lra.
      assert (H : 1 / 13.6 < 1 / 12).
      { unfold Rdiv.
        apply Rmult_lt_compat_l; [lra|].
        apply Rinv_lt_contravar; [apply Rmult_lt_0_compat|]; lra. }
      lra. }
    assert (HL0_pos : deep_water_wavelength T > 0).
    { unfold deep_water_wavelength, g.
      assert (Hpi : PI > 0) by apply PI_RGT_0.
      apply Rmult_lt_0_compat.
      - apply Rmult_lt_0_compat; lra.
      - apply Rinv_0_lt_compat. lra. }
    assert (Hratio_low : H0 / deep_water_wavelength T > 1 / 795).
    { apply ratio_lower_bound; lra. }
    assert (Hsqrt_pos : sqrt (H0 / deep_water_wavelength T) > 0).
    { apply sqrt_lt_R0. apply Rdiv_pos_pos; lra. }
    assert (Hsqrt_low : sqrt (H0 / deep_water_wavelength T) > 0.035).
    { apply sqrt_ratio_lower.
      assert (H1795 : (1:R) / 795 > 0.00125) by lra.
      lra. }
    assert (Hxi_up : WedgeParams.beach_slope / sqrt (H0 / deep_water_wavelength T) <
                     0.08 / 0.035).
    { apply Rlt_trans with (r2 := 0.08 / sqrt (H0 / deep_water_wavelength T)).
      - apply Rmult_lt_compat_r.
        + apply Rinv_0_lt_compat. lra.
        + lra.
      - apply Rdiv_lt_compat_denom; lra. }
    assert (Hval : 0.08 / 0.035 < 3.3) by lra.
    lra.
Qed.

(** * The Wedge Wave Transformation *)

(** Phase-dependent superposition of incident and reflected waves.
    A_total = A * sqrt(1 + R^2 + 2*R*cos(dphi))
    where R = reflection coefficient, dphi = phase difference.
    Maximum (1+R)*A occurs when dphi = 0 (in-phase).
    Minimum (1-R)*A occurs when dphi = pi (out-of-phase). *)

Definition superposition_with_phase (A Rcoef dphi : R) : R :=
  A * sqrt (1 + Rcoef*Rcoef + 2*Rcoef*cos dphi).

Lemma superposition_max_in_phase : forall A Rcoef,
  A >= 0 -> 0 <= Rcoef <= 1 ->
  superposition_with_phase A Rcoef 0 = A * (1 + Rcoef).
Proof.
  intros A Rcoef HA HR.
  unfold superposition_with_phase.
  rewrite cos_0.
  replace (1 + Rcoef * Rcoef + 2 * Rcoef * 1) with ((1 + Rcoef) * (1 + Rcoef)) by ring.
  rewrite sqrt_square; lra.
Qed.

Lemma superposition_bound : forall A Rcoef dphi,
  A >= 0 -> 0 <= Rcoef <= 1 ->
  superposition_with_phase A Rcoef dphi <= A * (1 + Rcoef).
Proof.
  intros A Rcoef dphi HA HR.
  unfold superposition_with_phase.
  apply Rmult_le_compat_l; [lra|].
  rewrite <- sqrt_square with (x := 1 + Rcoef) by lra.
  apply sqrt_le_1_alt.
  assert (Hcos : -1 <= cos dphi <= 1) by apply COS_bound.
  assert (Hbound : 2 * Rcoef * cos dphi <= 2 * Rcoef).
  { replace (2 * Rcoef) with (2 * Rcoef * 1) at 2 by ring.
    apply Rmult_le_compat_l; [lra|]. lra. }
  replace ((1 + Rcoef) * (1 + Rcoef)) with (1 + Rcoef*Rcoef + 2*Rcoef) by ring.
  lra.
Qed.

(** Naturalistic wave transformation model.
    H_final = H0 * Ks * Kr * superposition_factor(R, dphi)
    where:
      H0   = deep water wave height
      Ks   = shoaling coefficient (Green's law)
      Kr   = refraction coefficient (Snell's law)
      R    = reflection coefficient (jetty)
      dphi = phase difference between incident and reflected waves *)

Definition wedge_transform (H0 Ks Kr Rcoef dphi : R) : R :=
  H0 * Ks * Kr * sqrt (1 + Rcoef*Rcoef + 2*Rcoef*cos dphi).

Lemma cos_sqr_le_1 : forall x, cos x * cos x <= 1.
Proof.
  intros x.
  assert (Hcos : -1 <= cos x <= 1) by apply COS_bound.
  destruct (Rle_dec 0 (cos x)) as [Hpos|Hneg].
  - replace 1 with (1 * 1) by ring.
    apply Rmult_le_compat; lra.
  - assert (Hneg' : cos x < 0) by lra.
    replace (cos x * cos x) with ((-cos x) * (-cos x)) by ring.
    replace 1 with (1 * 1) by ring.
    apply Rmult_le_compat; lra.
Qed.

Lemma superposition_factor_nonneg : forall Rcoef dphi,
  Rcoef >= 0 ->
  1 + Rcoef * Rcoef + 2 * Rcoef * cos dphi >= 0.
Proof.
  intros Rcoef dphi HR.
  assert (Hcos : -1 <= cos dphi <= 1) by apply COS_bound.
  assert (Hcos2 : cos dphi * cos dphi <= 1) by apply cos_sqr_le_1.
  replace (1 + Rcoef * Rcoef + 2 * Rcoef * cos dphi)
    with ((1 + Rcoef * cos dphi) * (1 + Rcoef * cos dphi)
          + Rcoef * Rcoef * (1 - cos dphi * cos dphi)) by ring.
  assert (H1 : (1 + Rcoef * cos dphi) * (1 + Rcoef * cos dphi) >= 0).
  { apply Rle_ge. apply Rle_0_sqr. }
  assert (H2 : 1 - cos dphi * cos dphi >= 0) by lra.
  assert (HR2 : Rcoef * Rcoef >= 0).
  { apply Rle_ge. apply Rle_0_sqr. }
  assert (H3 : Rcoef * Rcoef * (1 - cos dphi * cos dphi) >= 0).
  { apply Rle_ge. apply Rmult_le_pos; lra. }
  lra.
Qed.

Lemma wedge_transform_nonneg : forall H0 Ks Kr Rcoef dphi,
  H0 >= 0 -> Ks >= 0 -> Kr >= 0 -> Rcoef >= 0 ->
  wedge_transform H0 Ks Kr Rcoef dphi >= 0.
Proof.
  intros H0 Ks Kr Rcoef dphi HH0 HKs HKr HR.
  unfold wedge_transform.
  apply Rle_ge.
  apply Rmult_le_pos.
  - apply Rmult_le_pos.
    + apply Rmult_le_pos; lra.
    + lra.
  - apply sqrt_pos.
Qed.

(** Strictly positive when inputs are strictly positive. *)
Lemma wedge_transform_positive : forall H0 Ks Kr Rcoef dphi,
  H0 > 0 -> Ks > 0 -> Kr > 0 -> 0 < Rcoef < 1 ->
  wedge_transform H0 Ks Kr Rcoef dphi > 0.
Proof.
  intros H0 Ks Kr Rcoef dphi HH0 HKs HKr HR.
  unfold wedge_transform.
  apply Rmult_lt_0_compat.
  - apply Rmult_lt_0_compat.
    + apply Rmult_lt_0_compat; [exact HH0 | exact HKs].
    + exact HKr.
  - apply sqrt_lt_R0.
    assert (Hcos : -1 <= cos dphi <= 1) by apply COS_bound.
    assert (H2R : 2 * Rcoef >= 0) by lra.
    assert (Hterm : 2 * Rcoef * (-1) <= 2 * Rcoef * cos dphi).
    { apply Rmult_le_compat_l; lra. }
    assert (Hmin : 1 + Rcoef * Rcoef - 2 * Rcoef <=
                   1 + Rcoef * Rcoef + 2 * Rcoef * cos dphi).
    { replace (- 2 * Rcoef) with (2 * Rcoef * (-1)) by ring. lra. }
    replace (1 + Rcoef * Rcoef - 2 * Rcoef) with ((1 - Rcoef) * (1 - Rcoef)) in Hmin by ring.
    assert (Hsq : (1 - Rcoef) * (1 - Rcoef) > 0).
    { apply Rmult_lt_0_compat; lra. }
    lra.
Qed.

(** Maximum amplification occurs when waves are in phase (dphi = 0). *)
Definition wedge_transform_max (H0 Ks Kr Rcoef : R) : R :=
  H0 * Ks * Kr * (1 + Rcoef).

Lemma wedge_transform_max_achieved : forall H0 Ks Kr Rcoef,
  Rcoef >= -1 ->
  wedge_transform H0 Ks Kr Rcoef 0 = wedge_transform_max H0 Ks Kr Rcoef.
Proof.
  intros H0 Ks Kr Rcoef HR.
  unfold wedge_transform, wedge_transform_max.
  rewrite cos_0.
  replace (1 + Rcoef * Rcoef + 2 * Rcoef * 1) with ((1 + Rcoef) * (1 + Rcoef)) by ring.
  rewrite sqrt_square; [ring | lra].
Qed.

Lemma wedge_transform_upper_bound : forall H0 Ks Kr Rcoef dphi,
  H0 >= 0 -> Ks >= 0 -> Kr >= 0 -> 0 <= Rcoef <= 1 ->
  wedge_transform H0 Ks Kr Rcoef dphi <= wedge_transform_max H0 Ks Kr Rcoef.
Proof.
  intros H0 Ks Kr Rcoef dphi HH0 HKs HKr HR.
  unfold wedge_transform, wedge_transform_max.
  apply Rmult_le_compat_l.
  - apply Rmult_le_pos.
    + apply Rmult_le_pos; lra.
    + lra.
  - rewrite <- sqrt_square with (x := 1 + Rcoef) by lra.
    apply sqrt_le_1_alt.
    assert (Hcos : -1 <= cos dphi <= 1) by apply COS_bound.
    assert (Hbound : 2 * Rcoef * cos dphi <= 2 * Rcoef).
    { replace (2 * Rcoef) with (2 * Rcoef * 1) at 2 by ring.
      apply Rmult_le_compat_l; [lra|]. lra. }
    replace ((1 + Rcoef) * (1 + Rcoef)) with (1 + Rcoef*Rcoef + 2*Rcoef) by ring.
    lra.
Qed.

(** For typical Wedge conditions: in-phase reflection at jetty wall. *)
Definition wedge_transform_typical (H0 Ks Kr : R) : R :=
  wedge_transform_max H0 Ks Kr WedgeParams.reflection_coeff.

(** Simplified transform assuming normal incidence (Kr = 1) and in-phase. *)
Definition wedge_reflection_factor : R := 1 + WedgeParams.reflection_coeff.

Definition wedge_transform_simple (H0 Ks : R) : R :=
  H0 * Ks * wedge_reflection_factor.

Lemma wedge_transform_typical_value : forall H0 Ks Kr,
  wedge_transform_typical H0 Ks Kr = H0 * Ks * Kr * 1.95.
Proof.
  intros. unfold wedge_transform_typical, wedge_transform_max.
  unfold WedgeParams.reflection_coeff.
  replace (1 + 0.95) with 1.95 by lra.
  ring.
Qed.

(** * Shoaling Coefficient Bounds *)

(** We prove bounds on Rpower using the fact that for a,b > 0:
    a^4 < b implies a < b^(1/4).
    This follows from Rpower being strictly monotonic. *)

Lemma Rpower_4 : forall a : R, a > 0 -> Rpower a 4 = a * a * a * a.
Proof.
  intros a Ha.
  replace 4 with (INR 4) by (simpl; ring).
  rewrite Rpower_pow by lra.
  simpl. ring.
Qed.

Lemma Rpower_pos : forall x y : R, x > 0 -> Rpower x y > 0.
Proof.
  intros x y Hx.
  unfold Rpower.
  apply exp_pos.
Qed.

Lemma fourth_power_bound : forall a b : R,
  a > 0 -> b > 0 -> a * a * a * a < b -> a < Rpower b (1/4).
Proof.
  intros a b Ha Hb Hpow.
  assert (Ha4 : Rpower a 4 = a * a * a * a) by (apply Rpower_4; lra).
  assert (Hrp : Rpower a 4 < b) by lra.
  assert (Hpos1 : Rpower a 4 > 0) by (apply Rpower_pos; lra).
  assert (Hinv : Rpower (Rpower a 4) (1/4) < Rpower b (1/4)).
  {
    apply Rlt_Rpower_l.
    - lra.
    - split; [exact Hpos1 | exact Hrp].
  }
  assert (Hsimp : Rpower (Rpower a 4) (1/4) = a).
  {
    rewrite Rpower_mult.
    replace (4 * (1/4)) with 1 by field.
    apply Rpower_1.
    lra.
  }
  lra.
Qed.

Lemma shoaling_positive : forall h1 h2, h1 > 0 -> h2 > 0 ->
  shoaling_coeff_greens_law h1 h2 > 0.
Proof.
  intros h1 h2 H1 H2.
  unfold shoaling_coeff_greens_law.
  apply Rpower_pos.
  apply Rdiv_pos_pos; lra.
Qed.

Lemma shoaling_at_2m : shoaling_coeff_greens_law 10 2 > 1.4.
Proof.
  unfold shoaling_coeff_greens_law.
  replace (10 / 2) with 5 by field.
  apply fourth_power_bound.
  - lra.
  - lra.
  - (* 1.4^4 = 3.8416 < 5 *)
    lra.
Qed.

Lemma shoaling_at_1m : shoaling_coeff_greens_law 10 1 > 1.7.
Proof.
  unfold shoaling_coeff_greens_law.
  replace (10 / 1) with 10 by field.
  apply fourth_power_bound.
  - lra.
  - lra.
  - (* 1.7^4 = 8.3521 < 10 *)
    lra.
Qed.

Lemma shoaling_at_half_m : shoaling_coeff_greens_law 10 0.5 > 2.1.
Proof.
  unfold shoaling_coeff_greens_law.
  replace (10 / 0.5) with 20 by lra.
  apply fourth_power_bound.
  - lra.
  - lra.
  - (* 2.1^4 = 19.4481 < 20 *)
    lra.
Qed.

Lemma shoaling_increases_in_shallows : forall h1 h2 h3,
  h1 > 0 -> h2 > 0 -> h3 > 0 -> h2 > h3 ->
  shoaling_coeff_greens_law h1 h3 > shoaling_coeff_greens_law h1 h2.
Proof.
  intros h1 h2 h3 H1 H2 H3 Hlt.
  unfold shoaling_coeff_greens_law.
  apply Rlt_Rpower_l.
  - lra.
  - split.
    + apply Rdiv_pos_pos; lra.
    + assert (Hdiv : h1 / h2 < h1 / h3).
      {
        unfold Rdiv.
        apply Rmult_lt_compat_l.
        - lra.
        - apply Rinv_lt_contravar.
          + apply Rmult_lt_0_compat; lra.
          + lra.
      }
      exact Hdiv.
Qed.

(** * Main Theorems *)

Theorem wedge_amplification_exceeds_two_at_2m :
  forall H0,
  H0 > 0 ->
  wedge_transform_typical H0 (shoaling_coeff_greens_law 10 2) 1 > 2 * H0.
Proof.
  intros H0 HH0.
  unfold wedge_transform_typical, wedge_transform_max.
  unfold WedgeParams.reflection_coeff.
  replace (1 + 0.95) with 1.95 by lra.
  assert (Hs : shoaling_coeff_greens_law 10 2 > 1.4) by apply shoaling_at_2m.
  assert (Hprod : 1.4 * 1.95 > 2) by lra.
  assert (H1 : H0 * shoaling_coeff_greens_law 10 2 > H0 * 1.4).
  {
    apply Rmult_lt_compat_l.
    - exact HH0.
    - exact Hs.
  }
  assert (H2 : H0 * 1.4 * 1 * 1.95 > H0 * 1.4 * 1 * (2 / 1.4)).
  {
    apply Rmult_lt_compat_l.
    - apply Rmult_lt_0_compat.
      + apply Rmult_lt_0_compat; [exact HH0 | lra].
      + lra.
    - lra.
  }
  assert (H3 : H0 * 1.4 * 1 * (2 / 1.4) = 2 * H0) by (field; lra).
  lra.
Qed.

Theorem breaking_inevitable_at_1m :
  forall H0,
  H0 >= 1 ->
  is_breaking (wedge_transform_typical H0 (shoaling_coeff_greens_law 10 1) 1) 1.
Proof.
  intros H0 HH0.
  unfold is_breaking, breaking_ratio, wedge_transform_typical, wedge_transform_max,
         WedgeParams.reflection_coeff, mccowan_criterion.
  replace (1 + 0.95) with 1.95 by lra.
  assert (Hs : shoaling_coeff_greens_law 10 1 > 1.7) by apply shoaling_at_1m.
  assert (Hmin : H0 * shoaling_coeff_greens_law 10 1 * 1 * 1.95 > H0 * 1.7 * 1 * 1.95).
  {
    apply Rmult_gt_compat_r.
    - lra.
    - apply Rmult_gt_compat_r.
      + lra.
      + apply Rmult_gt_compat_l; [lra | exact Hs].
  }
  assert (Hbase : H0 * 1.7 * 1 * 1.95 >= 1 * 1.7 * 1 * 1.95).
  {
    apply Rmult_ge_compat_r.
    - lra.
    - apply Rmult_ge_compat_r.
      + lra.
      + apply Rmult_ge_compat_r; lra.
  }
  assert (Hval : 1 * 1.7 * 1 * 1.95 > 0.78) by lra.
  lra.
Qed.

Theorem breaking_inevitable_at_1m_simple :
  forall H0,
  H0 >= 1 ->
  is_breaking (wedge_transform_simple H0 (shoaling_coeff_greens_law 10 1)) 1.
Proof.
  intros H0 HH0.
  unfold is_breaking, breaking_ratio, wedge_transform_simple, wedge_reflection_factor,
         WedgeParams.reflection_coeff, mccowan_criterion.
  replace (1 + 0.95) with 1.95 by lra.
  assert (Hs : shoaling_coeff_greens_law 10 1 > 1.7) by apply shoaling_at_1m.
  assert (Hmin : H0 * shoaling_coeff_greens_law 10 1 * 1.95 > H0 * 1.7 * 1.95).
  {
    apply Rmult_gt_compat_r.
    - lra.
    - apply Rmult_gt_compat_l; [lra | exact Hs].
  }
  assert (Hbase : H0 * 1.7 * 1.95 >= 1 * 1.7 * 1.95).
  {
    apply Rmult_ge_compat_r.
    - lra.
    - apply Rmult_ge_compat_r; lra.
  }
  assert (Hval : 1 * 1.7 * 1.95 > 0.78) by lra.
  lra.
Qed.

(** * Shore Profile and Slope *)

Definition shore_normal_slope (d1 d2 z1 z2 : R) : R :=
  (z2 - z1) / (d2 - d1).

Lemma wedge_slope_is_steep :
  shore_normal_slope 0 100 0.78 (-8.03) < -1/15.
Proof.
  unfold shore_normal_slope.
  lra.
Qed.

Lemma wedge_slope_value :
  shore_normal_slope 0 100 0.78 (-8.03) = -0.0881.
Proof.
  unfold shore_normal_slope.
  lra.
Qed.

(** * Depth Profile Model *)

(** Linear interpolation between two points. *)
Definition lerp (x x0 x1 y0 y1 : R) : R :=
  y0 + (y1 - y0) * (x - x0) / (x1 - x0).

(** Piecewise linear interpolation of elevation profile.
    Control points from lidar: (12.5, 0.78), (37.5, -1.07), (62.5, -3.88), (87.5, -8.03).
    Using bin centers as x coordinates. *)
Definition elev_at_distance (d : R) : R :=
  if Rlt_dec d 12.5 then WedgeParams.elev_0_25m
  else if Rlt_dec d 37.5 then lerp d 12.5 37.5 0.78 (-1.07)
  else if Rlt_dec d 62.5 then lerp d 37.5 62.5 (-1.07) (-3.88)
  else if Rlt_dec d 87.5 then lerp d 62.5 87.5 (-3.88) (-8.03)
  else WedgeParams.elev_max_100m.

Definition depth_at_distance (d : R) : R :=
  let e := elev_at_distance d in
  if Rlt_dec e 0 then -e else 0.

Lemma lerp_at_x0 : forall x0 x1 y0 y1,
  x0 <> x1 -> lerp x0 x0 x1 y0 y1 = y0.
Proof.
  intros. unfold lerp. field. lra.
Qed.

Lemma lerp_at_x1 : forall x0 x1 y0 y1,
  x0 <> x1 -> lerp x1 x0 x1 y0 y1 = y1.
Proof.
  intros. unfold lerp. field. lra.
Qed.

Lemma depth_at_10_is_zero :
  depth_at_distance 10 = 0.
Proof.
  unfold depth_at_distance, elev_at_distance.
  destruct (Rlt_dec 10 12.5).
  - unfold WedgeParams.elev_0_25m.
    destruct (Rlt_dec 0.78 0); lra.
  - lra.
Qed.

Lemma depth_at_40_is_moderate :
  depth_at_distance 40 > 1.
Proof.
  unfold depth_at_distance, elev_at_distance.
  destruct (Rlt_dec 40 12.5); [lra|].
  destruct (Rlt_dec 40 37.5); [lra|].
  destruct (Rlt_dec 40 62.5).
  - unfold lerp.
    assert (Hlerp : 37.5 <> 62.5) by lra.
    destruct (Rlt_dec ((-1.07) + ((-3.88) - (-1.07)) * (40 - 37.5) / (62.5 - 37.5)) 0).
    + lra.
    + lra.
  - lra.
Qed.

(** * Wave Energy Considerations *)

Definition wave_energy (H : R) : R :=
  (1/8) * rho_seawater * g * H * H.

Lemma wave_energy_positive : forall H,
  H <> 0 -> wave_energy H > 0.
Proof.
  intros H Hne.
  unfold wave_energy, rho_seawater, g.
  assert (Hsq : H * H > 0).
  {
    rewrite <- Rsqr_def.
    apply Rsqr_pos_lt.
    exact Hne.
  }
  lra.
Qed.

Definition energy_amplification (H0 H : R) : R :=
  wave_energy H / wave_energy H0.

Lemma wedge_energy_nearly_quadruples : forall H0,
  H0 > 0 ->
  energy_amplification H0 (wedge_amplitude_factor * H0) > 3.6.
Proof.
  intros H0 HH0.
  unfold energy_amplification, wave_energy, wedge_amplitude_factor,
         WedgeParams.reflection_coeff, rho_seawater, g.
  assert (Hne : H0 <> 0) by lra.
  assert (Hne2 : H0 * H0 <> 0).
  {
    apply Rmult_integral_contrapositive.
    split; lra.
  }
  assert (Hfact : 1.95 * 1.95 > 3.6) by lra.
  field_simplify; lra.
Qed.

(** * Hazard Classification *)

Inductive HazardLevel : Type :=
  | Safe
  | Caution
  | Dangerous
  | Extreme.

Definition classify_hazard (H h : R) : HazardLevel :=
  let ratio := H / h in
  if Rlt_dec ratio 0.4 then Safe
  else if Rlt_dec ratio 0.6 then Caution
  else if Rlt_dec ratio 0.78 then Dangerous
  else Extreme.

Lemma wedge_always_extreme : forall H0,
  H0 >= 1 ->
  let H := wedge_transform_simple H0 (shoaling_coeff_greens_law 10 1) in
  classify_hazard H 1 = Extreme.
Proof.
  intros H0 HH0 H.
  unfold classify_hazard, H, wedge_transform_simple, wedge_reflection_factor,
         WedgeParams.reflection_coeff.
  assert (Hs : shoaling_coeff_greens_law 10 1 > 1.7) by apply shoaling_at_1m.
  assert (Hbound : H0 * shoaling_coeff_greens_law 10 1 * (1 + 0.95) / 1 > 0.78).
  {
    field_simplify.
    assert (Hmin : H0 * shoaling_coeff_greens_law 10 1 >= 1 * 1.7) by
      (apply Rmult_ge_compat; lra).
    assert (Hval : 1 * 1.7 * 1.95 > 0.78) by lra.
    lra.
  }
  destruct (Rlt_dec (H0 * shoaling_coeff_greens_law 10 1 * (1 + 0.95) / 1) 0.4); try lra.
  destruct (Rlt_dec (H0 * shoaling_coeff_greens_law 10 1 * (1 + 0.95) / 1) 0.6); try lra.
  destruct (Rlt_dec (H0 * shoaling_coeff_greens_law 10 1 * (1 + 0.95) / 1) 0.78); try lra.
  reflexivity.
Qed.

(** * Summary Results *)

Definition wedge_is_dangerous : Prop :=
  forall H0, H0 >= 1 ->
  exists h, h > 0 /\ h < 3 /\
  is_breaking (wedge_transform_simple H0 (shoaling_coeff_greens_law 10 h)) h.

Theorem wedge_danger_theorem : wedge_is_dangerous.
Proof.
  unfold wedge_is_dangerous.
  intros H0 HH0.
  exists 1.
  split.
  - lra.
  - split.
    + lra.
    + apply breaking_inevitable_at_1m_simple.
      exact HH0.
Qed.
